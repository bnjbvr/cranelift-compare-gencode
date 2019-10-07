/// Legalize instructions by expansion.
///
/// Use x86-specific instructions if needed.
#[allow(unused_variables,unused_assignments,non_snake_case)]
pub fn x86_expand(
    inst: crate::ir::Inst,
    func: &mut crate::ir::Function,
    cfg: &mut crate::flowgraph::ControlFlowGraph,
    isa: &dyn crate::isa::TargetIsa,
) -> bool {
    use crate::ir::InstBuilder;
    use crate::cursor::{Cursor, FuncCursor};
    let mut pos = FuncCursor::new(func).at_inst(inst);
    pos.use_srcloc(inst);
    {
        match pos.func.dfg[inst].opcode() {
            ir::Opcode::Clz => {
                // Unwrap a << clz.i64(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I64
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << isub(c_sixty_three, index2).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let c_minus_one = pos.ins().iconst(ir::types::I64, -1);
                    let c_sixty_three = pos.ins().iconst(ir::types::I64, 63);
                    let (index1, r2flags) = pos.ins().x86_bsr(x);
                    let index2 = pos.ins().selectif(ir::types::I64, ir::condcodes::IntCC::Equal, r2flags, c_minus_one, index1);
                    let a = pos.func.dfg.replace(inst).isub(c_sixty_three, index2);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << clz.i32(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I32
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << isub(c_thirty_one, index2).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let c_minus_one = pos.ins().iconst(ir::types::I32, -1);
                    let c_thirty_one = pos.ins().iconst(ir::types::I32, 31);
                    let (index1, r2flags) = pos.ins().x86_bsr(x);
                    let index2 = pos.ins().selectif(ir::types::I32, ir::condcodes::IntCC::Equal, r2flags, c_minus_one, index1);
                    let a = pos.func.dfg.replace(inst).isub(c_thirty_one, index2);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Ctz => {
                // Unwrap a << ctz.i64(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I64
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << selectif(ir::condcodes::IntCC::Equal, r2flags, c_sixty_four, index1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let c_sixty_four = pos.ins().iconst(ir::types::I64, 64);
                    let (index1, r2flags) = pos.ins().x86_bsf(x);
                    let a = pos.func.dfg.replace(inst).selectif(ir::types::I64, ir::condcodes::IntCC::Equal, r2flags, c_sixty_four, index1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << ctz.i32(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I32
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << selectif(ir::condcodes::IntCC::Equal, r2flags, c_thirty_two, index1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let c_thirty_two = pos.ins().iconst(ir::types::I32, 32);
                    let (index1, r2flags) = pos.ins().x86_bsf(x);
                    let a = pos.func.dfg.replace(inst).selectif(ir::types::I32, ir::condcodes::IntCC::Equal, r2flags, c_thirty_two, index1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Fcmp => {
                // Unwrap a << fcmp(ir::condcodes::FloatCC::Equal, x, y)
                let (_, x, y, predicate) = if let crate::ir::InstructionData::FloatCompare {
                    cond,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        predicates::is_equal(cond, ir::condcodes::FloatCC::Equal)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << band(a1, a2).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().fcmp(ir::condcodes::FloatCC::Ordered, x, y);
                    let a2 = pos.ins().fcmp(ir::condcodes::FloatCC::UnorderedOrEqual, x, y);
                    let a = pos.func.dfg.replace(inst).band(a1, a2);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << fcmp(ir::condcodes::FloatCC::NotEqual, x, y)
                let (_, x, y, predicate) = if let crate::ir::InstructionData::FloatCompare {
                    cond,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        predicates::is_equal(cond, ir::condcodes::FloatCC::NotEqual)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << bor(a1, a2).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().fcmp(ir::condcodes::FloatCC::Unordered, x, y);
                    let a2 = pos.ins().fcmp(ir::condcodes::FloatCC::OrderedNotEqual, x, y);
                    let a = pos.func.dfg.replace(inst).bor(a1, a2);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << fcmp(ir::condcodes::FloatCC::LessThan, x, y)
                let (_, x, y, predicate) = if let crate::ir::InstructionData::FloatCompare {
                    cond,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        predicates::is_equal(cond, ir::condcodes::FloatCC::LessThan)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << fcmp(ir::condcodes::FloatCC::GreaterThan, y, x).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a = pos.func.dfg.replace(inst).fcmp(ir::condcodes::FloatCC::GreaterThan, y, x);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << fcmp(ir::condcodes::FloatCC::LessThanOrEqual, x, y)
                let (_, x, y, predicate) = if let crate::ir::InstructionData::FloatCompare {
                    cond,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        predicates::is_equal(cond, ir::condcodes::FloatCC::LessThanOrEqual)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << fcmp(ir::condcodes::FloatCC::GreaterThanOrEqual, y, x).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a = pos.func.dfg.replace(inst).fcmp(ir::condcodes::FloatCC::GreaterThanOrEqual, y, x);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << fcmp(ir::condcodes::FloatCC::UnorderedOrGreaterThan, x, y)
                let (_, x, y, predicate) = if let crate::ir::InstructionData::FloatCompare {
                    cond,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        predicates::is_equal(cond, ir::condcodes::FloatCC::UnorderedOrGreaterThan)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << fcmp(ir::condcodes::FloatCC::UnorderedOrLessThan, y, x).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a = pos.func.dfg.replace(inst).fcmp(ir::condcodes::FloatCC::UnorderedOrLessThan, y, x);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << fcmp(ir::condcodes::FloatCC::UnorderedOrGreaterThanOrEqual, x, y)
                let (_, x, y, predicate) = if let crate::ir::InstructionData::FloatCompare {
                    cond,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        predicates::is_equal(cond, ir::condcodes::FloatCC::UnorderedOrGreaterThanOrEqual)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << fcmp(ir::condcodes::FloatCC::UnorderedOrLessThanOrEqual, y, x).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a = pos.func.dfg.replace(inst).fcmp(ir::condcodes::FloatCC::UnorderedOrLessThanOrEqual, y, x);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Popcnt => {
                // Unwrap qv16 << popcnt.i64(qv1)
                let (qv1, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I64
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by qv16 << ushr_imm(qv15, 56).
                let r = pos.func.dfg.inst_results(inst);
                let qv16 = &r[0];
                let typeof_qv16 = pos.func.dfg.value_type(*qv16);
                if predicate {
                    let qv3 = pos.ins().ushr_imm(qv1, 1);
                    let qc77 = pos.ins().iconst(ir::types::I64, 8608480567731124087);
                    let qv4 = pos.ins().band(qv3, qc77);
                    let qv5 = pos.ins().isub(qv1, qv4);
                    let qv6 = pos.ins().ushr_imm(qv4, 1);
                    let qv7 = pos.ins().band(qv6, qc77);
                    let qv8 = pos.ins().isub(qv5, qv7);
                    let qv9 = pos.ins().ushr_imm(qv7, 1);
                    let qv10 = pos.ins().band(qv9, qc77);
                    let qv11 = pos.ins().isub(qv8, qv10);
                    let qv12 = pos.ins().ushr_imm(qv11, 4);
                    let qv13 = pos.ins().iadd(qv11, qv12);
                    let qc0F = pos.ins().iconst(ir::types::I64, 1085102592571150095);
                    let qv14 = pos.ins().band(qv13, qc0F);
                    let qc01 = pos.ins().iconst(ir::types::I64, 72340172838076673);
                    let qv15 = pos.ins().imul(qv14, qc01);
                    let qv16 = pos.func.dfg.replace(inst).ushr_imm(qv15, 56);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap lv16 << popcnt.i32(lv1)
                let (lv1, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I32
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by lv16 << ushr_imm(lv15, 24).
                let r = pos.func.dfg.inst_results(inst);
                let lv16 = &r[0];
                let typeof_lv16 = pos.func.dfg.value_type(*lv16);
                if predicate {
                    let lv3 = pos.ins().ushr_imm(lv1, 1);
                    let lc77 = pos.ins().iconst(ir::types::I32, 2004318071);
                    let lv4 = pos.ins().band(lv3, lc77);
                    let lv5 = pos.ins().isub(lv1, lv4);
                    let lv6 = pos.ins().ushr_imm(lv4, 1);
                    let lv7 = pos.ins().band(lv6, lc77);
                    let lv8 = pos.ins().isub(lv5, lv7);
                    let lv9 = pos.ins().ushr_imm(lv7, 1);
                    let lv10 = pos.ins().band(lv9, lc77);
                    let lv11 = pos.ins().isub(lv8, lv10);
                    let lv12 = pos.ins().ushr_imm(lv11, 4);
                    let lv13 = pos.ins().iadd(lv11, lv12);
                    let lc0F = pos.ins().iconst(ir::types::I32, 252645135);
                    let lv14 = pos.ins().band(lv13, lc0F);
                    let lc01 = pos.ins().iconst(ir::types::I32, 16843009);
                    let lv15 = pos.ins().imul(lv14, lc01);
                    let lv16 = pos.func.dfg.replace(inst).ushr_imm(lv15, 24);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Smulhi => {
                // Unwrap res_hi << smulhi(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::Binary {
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                let res_hi;
                {
                    let r = pos.func.dfg.inst_results(inst);
                    res_hi = r[0];
                }
                // typeof_x must belong to TypeSet(lanes={1}, ints={32, 64})
                let predicate = predicate && TYPE_SETS[0].contains(typeof_x);
                if predicate {
                    pos.func.dfg.clear_results(inst);
                    let (res_lo, res_hi) = pos.ins().with_results([None, Some(res_hi)]).x86_smulx(x, y);
                    let removed = pos.remove_inst();
                    debug_assert_eq!(removed, inst);
                    return true;
                }
            }

            ir::Opcode::Umulhi => {
                // Unwrap res_hi << umulhi(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::Binary {
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                let res_hi;
                {
                    let r = pos.func.dfg.inst_results(inst);
                    res_hi = r[0];
                }
                // typeof_x must belong to TypeSet(lanes={1}, ints={32, 64})
                let predicate = predicate && TYPE_SETS[0].contains(typeof_x);
                if predicate {
                    pos.func.dfg.clear_results(inst);
                    let (res_lo, res_hi) = pos.ins().with_results([None, Some(res_hi)]).x86_umulx(x, y);
                    let removed = pos.remove_inst();
                    debug_assert_eq!(removed, inst);
                    return true;
                }
            }

            ir::Opcode::FcvtFromUint => {
                expand_fcvt_from_uint(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::FcvtToSint => {
                expand_fcvt_to_sint(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::FcvtToSintSat => {
                expand_fcvt_to_sint_sat(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::FcvtToUint => {
                expand_fcvt_to_uint(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::FcvtToUintSat => {
                expand_fcvt_to_uint_sat(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::Fmax => {
                expand_minmax(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::Fmin => {
                expand_minmax(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::Sdiv => {
                expand_sdivrem(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::Srem => {
                expand_sdivrem(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::Udiv => {
                expand_udivrem(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::Urem => {
                expand_udivrem(inst, pos.func, cfg, isa);
                return true;
            }

            _ => {},
        }
    }
    crate::legalizer::expand_flags(inst, pos.func, cfg, isa)
}

/// Legalize instructions by narrowing.
///
/// Use x86-specific instructions if needed.
#[allow(unused_variables,unused_assignments,non_snake_case)]
pub fn x86_narrow(
    inst: crate::ir::Inst,
    func: &mut crate::ir::Function,
    cfg: &mut crate::flowgraph::ControlFlowGraph,
    isa: &dyn crate::isa::TargetIsa,
) -> bool {
    use crate::ir::InstBuilder;
    use crate::cursor::{Cursor, FuncCursor};
    let mut pos = FuncCursor::new(func).at_inst(inst);
    pos.use_srcloc(inst);
    {
        match pos.func.dfg[inst].opcode() {
            ir::Opcode::Splat => {
                // Unwrap y << splat.b8x16(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.ctrl_typevar(inst) == ir::types::B8X16
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by y << x86_pshufb(a, c).
                let r = pos.func.dfg.inst_results(inst);
                let y = &r[0];
                let typeof_y = pos.func.dfg.value_type(*y);
                if predicate {
                    let a = pos.ins().scalar_to_vector(ir::types::B8X16, x);
                    let b = pos.ins().f64const(0);
                    let c = pos.ins().raw_bitcast(ir::types::B8X16, b);
                    let y = pos.func.dfg.replace(inst).x86_pshufb(a, c);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap y << splat.i8x16(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.ctrl_typevar(inst) == ir::types::I8X16
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by y << x86_pshufb(a, c).
                let r = pos.func.dfg.inst_results(inst);
                let y = &r[0];
                let typeof_y = pos.func.dfg.value_type(*y);
                if predicate {
                    let a = pos.ins().scalar_to_vector(ir::types::I8X16, x);
                    let b = pos.ins().f64const(0);
                    let c = pos.ins().raw_bitcast(ir::types::I8X16, b);
                    let y = pos.func.dfg.replace(inst).x86_pshufb(a, c);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap y << splat.b16x8(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.ctrl_typevar(inst) == ir::types::B16X8
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by y << raw_bitcast.b16x8.i32x4(d).
                let r = pos.func.dfg.inst_results(inst);
                let y = &r[0];
                let typeof_y = pos.func.dfg.value_type(*y);
                if predicate {
                    let a = pos.ins().scalar_to_vector(ir::types::B16X8, x);
                    let b = pos.ins().insertlane(a, 1, x);
                    let c = pos.ins().raw_bitcast(ir::types::I32X4, b);
                    let d = pos.ins().x86_pshufd(c, 0);
                    let y = pos.func.dfg.replace(inst).raw_bitcast(ir::types::B16X8, d);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap y << splat.i16x8(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.ctrl_typevar(inst) == ir::types::I16X8
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by y << raw_bitcast.i16x8.i32x4(d).
                let r = pos.func.dfg.inst_results(inst);
                let y = &r[0];
                let typeof_y = pos.func.dfg.value_type(*y);
                if predicate {
                    let a = pos.ins().scalar_to_vector(ir::types::I16X8, x);
                    let b = pos.ins().insertlane(a, 1, x);
                    let c = pos.ins().raw_bitcast(ir::types::I32X4, b);
                    let d = pos.ins().x86_pshufd(c, 0);
                    let y = pos.func.dfg.replace(inst).raw_bitcast(ir::types::I16X8, d);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap y << splat.b32x4(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.ctrl_typevar(inst) == ir::types::B32X4
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by y << x86_pshufd(a, 0).
                let r = pos.func.dfg.inst_results(inst);
                let y = &r[0];
                let typeof_y = pos.func.dfg.value_type(*y);
                if predicate {
                    let a = pos.ins().scalar_to_vector(ir::types::B32X4, x);
                    let y = pos.func.dfg.replace(inst).x86_pshufd(a, 0);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap y << splat.i32x4(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.ctrl_typevar(inst) == ir::types::I32X4
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by y << x86_pshufd(a, 0).
                let r = pos.func.dfg.inst_results(inst);
                let y = &r[0];
                let typeof_y = pos.func.dfg.value_type(*y);
                if predicate {
                    let a = pos.ins().scalar_to_vector(ir::types::I32X4, x);
                    let y = pos.func.dfg.replace(inst).x86_pshufd(a, 0);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap y << splat.f32x4(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.ctrl_typevar(inst) == ir::types::F32X4
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by y << x86_pshufd(a, 0).
                let r = pos.func.dfg.inst_results(inst);
                let y = &r[0];
                let typeof_y = pos.func.dfg.value_type(*y);
                if predicate {
                    let a = pos.ins().scalar_to_vector(ir::types::F32X4, x);
                    let y = pos.func.dfg.replace(inst).x86_pshufd(a, 0);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap y << splat.b64x2(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.ctrl_typevar(inst) == ir::types::B64X2
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by y << insertlane(a, 1, x).
                let r = pos.func.dfg.inst_results(inst);
                let y = &r[0];
                let typeof_y = pos.func.dfg.value_type(*y);
                if predicate {
                    let a = pos.ins().scalar_to_vector(ir::types::B64X2, x);
                    let y = pos.func.dfg.replace(inst).insertlane(a, 1, x);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap y << splat.i64x2(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.ctrl_typevar(inst) == ir::types::I64X2
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by y << insertlane(a, 1, x).
                let r = pos.func.dfg.inst_results(inst);
                let y = &r[0];
                let typeof_y = pos.func.dfg.value_type(*y);
                if predicate {
                    let a = pos.ins().scalar_to_vector(ir::types::I64X2, x);
                    let y = pos.func.dfg.replace(inst).insertlane(a, 1, x);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap y << splat.f64x2(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.ctrl_typevar(inst) == ir::types::F64X2
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by y << insertlane(a, 1, x).
                let r = pos.func.dfg.inst_results(inst);
                let y = &r[0];
                let typeof_y = pos.func.dfg.value_type(*y);
                if predicate {
                    let a = pos.ins().scalar_to_vector(ir::types::F64X2, x);
                    let y = pos.func.dfg.replace(inst).insertlane(a, 1, x);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Extractlane => {
                convert_extractlane(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::Ineg => {
                convert_ineg(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::Insertlane => {
                convert_insertlane(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::Shuffle => {
                convert_shuffle(inst, pos.func, cfg, isa);
                return true;
            }

            _ => {},
        }
    }
    crate::legalizer::narrow_flags(inst, pos.func, cfg, isa)
}

// Table of value type sets.
const TYPE_SETS: [ir::instructions::ValueTypeSet; 1] = [
    ir::instructions::ValueTypeSet {
        // TypeSet(lanes={1}, ints={32, 64})
        lanes: BitSet::<u16>(1),
        ints: BitSet::<u8>(96),
        floats: BitSet::<u8>(0),
        bools: BitSet::<u8>(0),
        refs: BitSet::<u8>(0),
    },
];
pub static LEGALIZE_ACTIONS: [isa::Legalize; 5] = [
    crate::legalizer::expand_flags,
    crate::legalizer::widen,
    x86_expand,
    x86_narrow,
    crate::legalizer::narrow_flags,
];
