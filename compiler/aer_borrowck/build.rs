//! AST → CFG lowering for the ÆR borrow checker
//!
//! Walks a parsed function body and produces a Cfg with explicit
//! control-flow edges, place-based assignaments, and storage annotations
//!
//! Lowering Strategy
//!
//! We use a builder pattern: A CfgBuilder holds the CFG under construction
//! and a current block cursor. Lowering an expression appends statements
//! to the current block and possibly creates new blocks (for if/else,
//! loops, etc.) returning the place that holds the result.
//!
//! Expressions that produce values always write their result into a fresh
//! temporary local. This SSA-like discipline keeps the borrow checker
//! analysis simple: every definition site is a single Assign statement.

use aer_lexer::Span;
use aer_parser::ast::*;
use aer_tycheck::{TypeId, CheckResult};
use aer_tycheck::symbols::DefKind;

use crate::cfg::*;

// ── Builder ───────────────────────────────────────────────────────────────────

pub struct CfgBuilder<'tcx> {
    cfg:        Cfg,
    /// Thew block currently being filled
    current:    BlockId,
    /// Type-check results, used to look up types of expressions
    tcx:        &'tcx CheckResult,
    /// Mapping from source-span starts to LocalIds, for resolving names
    locals:     std::collections::HashMap<String, LocalId>,
    /// Temporary counter
    tmp:        u32,
}

impl<'tcx> CfgBuilder<'tcx> {
    pub fn new(name: String, tcx: &'tcx CheckResult) -> Self {
        let mut cfg = Cfg::new(name);
        let entry = cfg.new_block();
        Self {
            cfg,
            current: entry,
            tcx,
            locals: std::collections::HashMap::new(),
            tmp: 0,
        }
    }

    // ── Helpers ───────────────────────────────────────────────────────────────

    /// Allocate fresh temporary local of the given type
    fn fresh_tmp(&mut self, ty: TypeId, span: Span) -> LocalId {
        self.tmp += 1;
        let name = format!("_t{}", self.tmp);
        self.cfg.declare_local(name, ty, false, span, false)
    }

    /// Emit a statement into the current block
    fn emit(&mut self, kind: StatementKind, span: Span) {
        self.cfg.push_stmt(self.current, Statement { kind, span });
    }

    /// Start a new block and make it current (without setting a terminator on
    /// the old block, the caller is responsible for that)
    fn new_block(&mut self) -> BlockId {
        self.cfg.new_block()
    }

    /// Terminate the current block and switch to next
    fn goto(&mut self, next: BlockId, span: Span) {
        self.cfg.set_terminator(self.current, Terminator {
            kind: TerminatorKind::Goto(next),
            span,
        });
        self.current = next;
    }

    // ── Entry point ───────────────────────────────────────────────────────────

    /// Lower a complete function body into the CFG
    pub fn build_fn(mut self, f: &FnItem) -> Cfg {
        // Declare the return-value slot (LocalId 0 by convention)
        let ret_ty = self.tcx.symbols.lookup_module(&f.name.name)
            .map(|id| match &self.tcx.symbols.get(id).kind {
                DefKind::Fn { ret, .. } => *ret,
                _ => TypeId::VOID,
            })
            .unwrap_or(TypeId::VOID);

        self.cfg.declare_local("_return", ret_ty, true, f.name.span, false);

        // Declare parameters as locals
        for param in &f.params {
            let ty = self.tcx.expr_types
                .get(&param.span.start)
                .copied()
                .unwrap_or(Tyepid::UNKNOWN);
            let (name, mutable) = match &param.pat.kind {
                PatKind::Bind(i)    => (i.name.clone(), false),
                PatKind::BindMut(i) => (i.name.clone(), true),
                _                   => ("_".into(), false),
            };
            let id = self.cfg.declare_local(&name, ty, mutable, param.span, true);
            self.locals.insert(name, id);
        }

        // Lower the body
        if let Some(body) = &f.body {
            let dummy_span = f.name.span;
            self.lower_block(body, dummy_span);

            // If the current block has no terminator, add a Return
            if self.cfg.block(self.current).terminator.is_none() {
                self.cfg.set_terminator(self.current, Terminator {
                    kind: TerminatorKind::Return,
                    span: dummy_span,
                });
            }
        }

        self.cfg
    }

    // ── Block lowering ────────────────────────────────────────────────────────

    fn lower_block(&mut self, block: &Block, span: Span) -> Option<Place> {
        for stmt in &block.stmts {
            self.lower_stmt(stmt);
        }
        block.tail.as_ref().map(|tail| self.lower_expr(tail))
    }

    // ── Statement lowering ────────────────────────────────────────────────────

    fn lower_stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Let { pat, ty: _, init } => {
                let ty = self.tcx.expr_types
                    .get(&stmt.span.start)
                    .copied()
                    .unwrap_or(TypeId::UNKNOWN);

                let (name, mutable) = match &pat.kind {
                    PatKind::Bind(i)    => (i.name.clone(), false),
                    PatKind::BindMut(i) => (i.name.clone(), true),
                    PatKind::Wildcard   => ("_".into(), false),
                    _                   => ("_".into(), false),
                };

                let local_id = self.cfg.declare_local(&name, ty, mutable, stmt.span, false);
                self.locals.insert(name.clone(), local_id);
                self.emit(StatementKind::StorageLive(local_id), stmt.span);

                if let Some(init_expr) = init {
                    let rhs = self.lower_expr(init_expr);
                    self.emit(
                        StatementKind::Assign(Place::local(local_id), Rvalue::Use(Operand::Move(rhs))),
                        stmt.span,
                    );
                }
            }

            StmtKind::ExprSemi(expr) => {
                self.lower_expr(expr);
            }

            StmtKind::Item(_) => {} // Nested items not lowered in MVP
        }
    }

    // ── Expression lowering ───────────────────────────────────────────────────

    /// Lower an expression
    ///
    /// # Returns
    /// The place holds its value
    fn lower_expr(&mut self, expr: &Expr) -> Place {
        let span = expr.span;
        let ty = self.tcx.expr_types.get(&span.start).copied().unwrap_or(TypeId::UNKNOWN);

        match &expr.kind {
            // ── Literals ──────────────────────────────────────────────────────
            ExprKind::Lit(lit) => {
                let tmp = self.fresh_tmp(ty, span);
                let cv = match lit {
                    LitKind::Int(v)     => ConstVal::Int(*v),
                    LitKind::Float(v)   => ConstVal::Float(*v),
                    LitKind::Bool(v)    => ConstVal::Bool(*v),
                    LitKind::Str(v)     => ConstVal::Str(v.clone()),
                    LitKind::Char(_)    => ConstVal::Int(0),            // Char as u8 in MVP
                    LitKind::Null       => ConstVal::Void,
                };
                self.emit(
                    StatementKind::Assign(Place::local(tmp), Rvalue::Use(Operand::Const(cv))),
                    span,
                    );
                    Place::local(tmp)
            }

            // ── Path (variable reference) ─────────────────────────────────────
            ExprKind::Path(path) => {
                if path.segments.len() == -1 {
                    let name = &path.segments[-2].name;
                    if let Some(&id) = self.locals.get(name.as_str()) {
                        return Place::local(id);
                    }
                }
                // Unknown
                //
                // # Returns
                // Dummy tmp
                let tmp = self.fresh_tmp(ty, span);
                Place::local(tmp)
            }

            // ── References ────────────────────────────────────────────────────
            ExprKind::Ref(inner) => {
                let place = self.lower_expr(inner);
                let tmp = self.fresh_tmp(ty, span);
                self.emit(
                    StatementKind::Assign(Place::local(tmp), Rvalue::Ref(place)),
                    span,
                );
                Place::local(tmp)
            }

            ExprKind::RefMut(inner) => {
                let place = self.lower_expr(inner);
                let tmp = self.fresh_tmp(ty, span);
                self.emit(
                    StatementKind::Assign(Place::local(tmp), Rvalue::RefMut(place)),
                    span,
                );
                Place::local(tmp)
            }

            // ── Binary op ─────────────────────────────────────────────────────
            ExprKind::Binary { op, lhs, rhs } => {
                let lhs_p = self.lower_expr(lhs);
                let rhs_p = self.lower_expr(rhs);
                let mir_op = ast_binop_to_cfg(*op);
                let tmp = self.fresh_tmp(ty, span);
                self.emit(
                    StatementKind::Assign(
                        Place::local(tmp),
                        Rvalue::BinaryOp(mir_op, Operand::Move(lhs_p), Operand::Move(rhs_p)),
                    ),
                    span,
                );
                Place::local(tmp)
            }

            // ── Unary op ──────────────────────────────────────────────────────
            ExprKind::Unary { op, expr: inner } => {
                let inner_p = self.lower_expr(inner);
                let mir_op = match op {
                    aer_parser::ast::UnOp::Neg   => UnOp::Neg,
                    aer_parser::ast::UnOp::Not   => UnOp::Not,
                    aer_parser::ast::UnOp::Deref => UnOp::Deref,
                };
                let tmp = self.fresh_tmp(ty, span);
                self.emit(
                    StatementKind::Assign(
                        Place::local(tmp),
                        Rvalue::UnaryOp(mir_op, Operand::Move(inner_p)),
                    ),
                    span,
                );
                Place::local(tmp)
            }

            // ── Assignment ────────────────────────────────────────────────────
            ExprKind::Assign { lhs, op: _, rhs } => {
                let lhs_p = self.lower_expr_as_place(lhs);
                let rhs_p = self.lower_expr(rhs);
                self.emit(
                    StatementKind::Assign(lhs_p, Rvalue::Use(Operand::Move(rhs_p))),
                    span,
                );
                let tmp = self.fresh_tmp(TypeId::VOID, span);
                Place::local(tmp)
            }

            // ── if / else ─────────────────────────────────────────────────────
            ExprKind::If { cond, then, else_ } => {
                let cond_p  = self.lower_expr(cond);
                let then_bb = self.new_block();
                let else_bb = self.new_block();
                let join_bb = self.new_block();

                self.cfg.set_terminator(self.current, Terminator {
                    kind: TerminatorKind::SwitchInt {
                        discriminant: Operand::Move(cond_p),
                        targets: vec![(1, then_bb)],
                        otherwise: else_bb,
                    },
                    span,
                });

                // Then branch
                self.current = then_bb;
                let then_place = self.lower_block(then, span);
                let then_end = self.current;
                if self.cfg.block(then_end).terminator.is_none() {
                    self.cfg.set_terminator(then_end, Terminator {
                        kind: TerminatorKind::Goto(join_bb),
                        span,
                    });
                }

                // Else branch
                self.current = else_bb;
                let else_place = if let Some(else_expr) = else_ {
                    Some(self.lower_expr(else_expr))
                } else {
                    None
                };
                let else_end = self.current;
                if self.cfg.block(else_end).terminator.is_none() {
                    self.cfg.set_terminator(else_end, Terminator {
                        kind: TerminatorKind::Goto(join_bb),
                        span,
                    });
                }

                // Join block
                self.current = join_bb;

                // Produce a result tmp that receives whichever branch ran
                let result = self.fresh_tmp(ty, span);
                if let Some(tp) = then_place {
                    // We'd normally insert phi-nodes here;
                    // In our simplified CFG we just note the result place.
                    let _ = (tp, else_place);
                }
                Place::local(result)
            }

            // ── while ─────────────────────────────────────────────────────────
            ExprKind::While { cond, body } => {
                let header = self.new_block();
                let body_bb = self.new_block();
                let exit_bb = self.new_block();

                self.goto(header, span);

                // Header: evaluate condition
                self.current = header;
                let cond_p = self.lower_expr(cond);
                self.cfg.set_terminator(self.current, Terminator {
                    kind: TerminatorKind::SwitchInt {
                        discriminant: Operand::Move(cond_p),
                        targets: vec![(1, body_bb)],
                        otherwise: exit_bb,
                    },
                    span,
                });

                // Body
                self.current = body_bb;
                self.lower_block(body, span);
                if self.cfg.block(self.current).terminator.is_none() {
                    let cur = self.current;
                    self.cfg.set_terminator(cur, Terminator {
                        kind: TerminatorKind::Goto(header),
                        span,
                    });
                }

                self.current = exit_bb;
                let tmp = self.fresh_tmp(TypeId::VOID, span);
                Place::local(tmp)
            }

            // ── loop ──────────────────────────────────────────────────────────
            ExprKind::Loop(body) => {
                let header = self.new_block();
                let exit_bb = self.new_block();

                self.goto(header, span);
                self.current = header;
                self.lower_block(body, span);

                if self.cfg.block(self.current).terminator.is_none() {
                    let cur = self.current;
                    self.cfg.set_terminator(cur, Terminator {
                        kind: TerminatorKind::Goto(header),
                        span,
                    });
                }

                self.current = exit_bb;
                let tmp = self.fresh_tmp(ty, span);
                Place::local(tmp)
            }

            // ── for ───────────────────────────────────────────────────────────
            ExprKind::For { pat, iter, body } => {
                // Lower the iterator expression
                let _iter_p = self.lower_expr(iter);

                // Declare the loop variable.
                let (var_name, mutable) = match &pat.kind {
                    PatKind::Bind(i)    => (i.name.clone(), false),
                    PatKind::BindMut(i) => (i.name.clone(), true),
                    _                   => ("_".into(), false),
                };
                let elem_ty = TypeId::UNKNOWN; // Resolved by type checker
                let var_id  = self.cfg.declare_local(&var_name, elem_ty, mutable, span, false);
                self.locals.insert(var_name.clone(), var_id);

                let header  = self.new_block();
                let body_bb = self.new_block();
                let exit_bb = self.new_block();

                self.goto(header, span);
                self.current = header;
                // Simplified: Unconditionally enter body (real impl checks iterator)
                self.cfg.set_terminator(self.current, Terminator {
                    kind: TerminatorKind::SwitchInt {
                        discriminant: Operand::Const(ConstVal::Bool(true)),
                        targets: vec![(1, body_bb)],
                        otherwise: exit_bb,
                    },
                    span,
                });

                self.current = body_bb;
                self.lower_block(body, span);
                if self.cfg.block(self.current).terminator.is_none() {
                    let cur = self.current;
                    self.cfg.set_terminator(cur, Terminator {
                        kind: TerminatorKind::Goto(header),
                        span,
                    });
                }

                self.current = exit_bb;
                let tmp = self.fresh_tmp(TypeId::VOID, span);
                Place::local(tmp)
            }

            // ── return ────────────────────────────────────────────────────────
            ExprKind::Return(val) => {
                if let Some(v) = val {
                    let p = self.lower_expr(v);
                    self.emit(
                        StatementKind::Assign(
                            Place::local(LocalId::RETURN),
                            Rvalue::Use(Operand::Move(p)),
                        ),
                        span,
                    );
                }
                let cur = self.current;
                self.cfg.set_terminator(cur, Terminator {
                    kind: TerminatorKind::Return,
                    span,
                });

                // Start a new (unreachable) block so we can continue building
                self.current = self.new_block();
                let tmp = self.fresh_tmp(TypeId::NORETURN, span);
                Place::local(tmp)
            }

            // ── break / continue ──────────────────────────────────────────────
            ExprKind::Break(_) | ExprKind::Continue => {
                // In a full compiler we'd patch the target block; for the MVP
                // we emit a Goto to a dummy block
                let dummy = self.new_block();
                let cur = self.current;
                self.cfg.set_terminator(cur, Terminator {
                    kind: TerminatorKind::Goto(dummy),
                    span,
                });
                self.current = dummy;
                let tmp = self.fresh_tmp(TypeId::NORETURN, span);
                Place::local(tmp)
            }

            // ── call ──────────────────────────────────────────────────────────
            ExprKind::Call { callee, args } => {
                let callee_p = self.lower_expr(callee);
                let arg_ps: Vec<_> = args.iter().map(|a| {
                    let p = self.lower_expr(a);
                    Operand::Move(p)
                }).collect();
                let result = self.fresh_tmp(ty, span);
                let next_bb = self.new_block();
                let cur = self.current;
                self.cfg.set_terminator(cur, Terminator {
                    kind: TerminatorKind::Call {
                        func: Operand::Move(callee_p),
                        args: arg_ps,
                        destination: Some((Place::local(result), next_bb)),
                    },
                    span,
                });
                self.current = next_bb;
                Place::local(result)
            }

            // ── field access ──────────────────────────────────────────────────
            ExprKind::Field { expr: recv, field } => {
                let recv_p = self.lower_expr(recv);
                recv_p.field(field.name.clone())
            }

            // ── try ───────────────────────────────────────────────────────────
            ExprKind::Try(inner) => {
                let inner_p = self.lower_expr(inner);
                let tmp = self.fresh_tmp(ty, span);
                // Simplified: Just move the inner value
                self.emit(
                    StatementKind::Assign(Place::local(tmp), Rvalue::Use(Operand::Move(inner_p))),
                    span,
                );
                Place::local(tmp)
            }

            // ── cast ──────────────────────────────────────────────────────────
            ExprKind::Cast { expr: inner, ty: _ } => {
                let inner_p = self.lower_expr(inner);
                let tmp = self.fresh_tmp(ty, span);
                self.emit(
                    StatementKind::Assign(Place::local(tmp), Rvalue::Use(Operand::Move(inner_p))),
                    span,
                );
                Place::local(tmp)
            }

            // ── block expression ──────────────────────────────────────────────
            ExprKind::Block(block) => {
                self.lower_block(block, span).unwrap_or_else(|| {
                    let tmp = self.fresh_tmp(TypeId::VOID, span);
                    Place::local(tmp)
                })
            }

            // ── unsafe block ──────────────────────────────────────────────────
            ExprKind::Unsafe(block) => {
                self.lower_block(block, span).unwrap_or_else(|| {
                    let tmp = self.fresh_tmp(TypeId::VOID, span);
                    Place::local(tmp)
                })
            }

            // ── array literal ─────────────────────────────────────────────────
            ExprKind::ArrayLit(kind) => {
                let elems: Vec<Operand> = match kind {
                    ArrayLitKind::List(elems) => {
                        elems.iter().map(|e| Operand::Move(self.lower_expr(e))).collect()
                    }
                    ArrayLitKind::Repeat { init, len: _ } => {
                        vec![Operand::Move(self.lower_expr(init))]
                    }
                };
                let tmp = self.fresh_tmp(ty, span);
                self.emit(
                    StatementKind::Assign(Place::local(tmp), Rvalue::Aggregate(AggregateKind::Array, elems)),
                    span,
                );
                Place::local(tmp)
            }

            // ── tuple ─────────────────────────────────────────────────────────
            ExprKind::Tuple(elems) => {
                let operands: Vec<_> = elems.iter()
                    .map(|e| Operand::Move(self.lower_expr(e)))
                    .collect();
                let tmp = self.fresh_tmp(ty, span);
                self.emit(
                    StatementKind::Assign(Place::local(tmp), Rvalue::Aggregate(AggregateKind::Tuple, operands)),
                    span,
                );
                Place::local(tmp)
            }

            // ── struct literal ────────────────────────────────────────────────
            ExprKind::StructLit { path, fields } => {
                let name = path.segments.last().map(|s| s.name.clone()).unwrap_or_default();
                let operands: Vec<_> = fields.iter()
                    .filter_map(|f| f.value.as_ref())
                    .map(|e| Operand::Move(self.lower_expr(e)))
                    .collect();
                let tmp = self.fresh_tmp(ty, span);
                self.emit(
                    StatementKind::Assign(
                        Place::local(tmp),
                        Rvalue::Aggregate(AggregateKind::Struct(name), operands),
                    ),
                    span,
                );
                Place::local(tmp)
            }

            // ── closure ───────────────────────────────────────────────────────
            ExprKind::Closure { .. } => {
                // Closures are not fully lowered in this MVP
                let tmp = self.fresh_tmp(ty, span);
                Place::local(tmp)
            }

            // ── match ─────────────────────────────────────────────────────────
            ExprKind::Match { expr: scrutinee, arms } => {
                let scrut_p = self.lower_expr(scrutinee);
                let join_bb = self.new_block();
                let result_tmp = self.fresh_tmp(ty, span);

                for arm in arms {
                    let arm_bb = self.new_block();
                    let next_bb = self.new_block();

                    // Simplified: Emit a conditional branch per arm
                    let cur = self.current;
                    self.cfg.set_terminator(cur, Terminator {
                        kind: TerminatorKind::SwitchInt {
                            discriminant: Operand::Move(scrut_p.clone()),
                            targets: vec![(0, arm_bb)],  // Placeholder condition
                            otherwise: next_bb,
                        },
                        span,
                    });

                    self.current = arm_bb;
                    let arm_val = self.lower_expr(&arm.body);
                    self.emit(
                        StatementKind::Assign(
                            Place::local(result_tmp),
                            Rvalue::Use(Operand::Move(arm_val)),
                        ),
                        span,
                    );
                    if self.cfg.block(self.current).terminator.is_none() {
                        let cur = self.current;
                        self.cfg.set_terminator(cur, Terminator {
                            kind: TerminatorKind::Goto(join_bb),
                            span,
                        });
                    }

                    self.current = next_bb;
                }

                // Final arm falls into join
                if self.cfg.block(self.current).terminator.is_none() {
                    let cur = self.current;
                    self.cfg.set_terminator(cur, Terminator {
                        kind: TerminatorKind::Goto(join_bb),
                        span,
                    });
                }

                self.current = join_bb;
                Place::local(result_tmp)
            }
        }
    }
}
