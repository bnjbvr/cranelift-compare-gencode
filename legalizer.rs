/// Legalize instructions by expansion.
///
/// Rewrite instructions in terms of other instructions, generally
/// operating on the same types as the original instructions.
#[allow(unused_variables,unused_assignments,non_snake_case)]
pub fn expand(
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
            ir::Opcode::BandImm => {
                // Unwrap a << band_imm(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << band(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iconst(typeof_x, y);
                    let a = pos.func.dfg.replace(inst).band(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::BandNot => {
                // Unwrap a << band_not(x, y)
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
                // Results handled by a << band(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().bnot(y);
                    let a = pos.func.dfg.replace(inst).band(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Bitrev => {
                // Unwrap a << bitrev.i32(x)
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
                // Results handled by a << bor(e1, e2).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().band_imm(x, 2863311530);
                    let a2 = pos.ins().ushr_imm(a1, 1);
                    let a3 = pos.ins().band_imm(x, 1431655765);
                    let a4 = pos.ins().ishl_imm(a3, 1);
                    let b = pos.ins().bor(a2, a4);
                    let b1 = pos.ins().band_imm(b, 3435973836);
                    let b2 = pos.ins().ushr_imm(b1, 2);
                    let b3 = pos.ins().band_imm(b, 858993459);
                    let b4 = pos.ins().ishl_imm(b3, 2);
                    let c = pos.ins().bor(b2, b4);
                    let c1 = pos.ins().band_imm(c, 4042322160);
                    let c2 = pos.ins().ushr_imm(c1, 4);
                    let c3 = pos.ins().band_imm(c, 252645135);
                    let c4 = pos.ins().ishl_imm(c3, 4);
                    let d = pos.ins().bor(c2, c4);
                    let d1 = pos.ins().band_imm(d, 4278255360);
                    let d2 = pos.ins().ushr_imm(d1, 8);
                    let d3 = pos.ins().band_imm(d, 16711935);
                    let d4 = pos.ins().ishl_imm(d3, 8);
                    let e = pos.ins().bor(d2, d4);
                    let e1 = pos.ins().ushr_imm(e, 16);
                    let e2 = pos.ins().ishl_imm(e, 16);
                    let a = pos.func.dfg.replace(inst).bor(e1, e2);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << bitrev.i64(x)
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
                // Results handled by a << bor(f1, f2).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().band_imm(x, -6148914691236517206);
                    let a2 = pos.ins().ushr_imm(a1, 1);
                    let a3 = pos.ins().band_imm(x, 6148914691236517205);
                    let a4 = pos.ins().ishl_imm(a3, 1);
                    let b = pos.ins().bor(a2, a4);
                    let b1 = pos.ins().band_imm(b, -3689348814741910324);
                    let b2 = pos.ins().ushr_imm(b1, 2);
                    let b3 = pos.ins().band_imm(b, 3689348814741910323);
                    let b4 = pos.ins().ishl_imm(b3, 2);
                    let c = pos.ins().bor(b2, b4);
                    let c1 = pos.ins().band_imm(c, -1085102592571150096);
                    let c2 = pos.ins().ushr_imm(c1, 4);
                    let c3 = pos.ins().band_imm(c, 1085102592571150095);
                    let c4 = pos.ins().ishl_imm(c3, 4);
                    let d = pos.ins().bor(c2, c4);
                    let d1 = pos.ins().band_imm(d, -71777214294589696);
                    let d2 = pos.ins().ushr_imm(d1, 8);
                    let d3 = pos.ins().band_imm(d, 71777214294589695);
                    let d4 = pos.ins().ishl_imm(d3, 8);
                    let e = pos.ins().bor(d2, d4);
                    let e1 = pos.ins().band_imm(e, -281470681808896);
                    let e2 = pos.ins().ushr_imm(e1, 16);
                    let e3 = pos.ins().band_imm(e, 281470681808895);
                    let e4 = pos.ins().ishl_imm(e3, 16);
                    let f = pos.ins().bor(e2, e4);
                    let f1 = pos.ins().ushr_imm(f, 32);
                    let f2 = pos.ins().ishl_imm(f, 32);
                    let a = pos.func.dfg.replace(inst).bor(f1, f2);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Bnot => {
                // Unwrap a << bnot(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << bxor(x, y).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_x must belong to TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[0].contains(typeof_x);
                if predicate {
                    let y = pos.ins().iconst(typeof_x, -1);
                    let a = pos.func.dfg.replace(inst).bxor(x, y);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::BorImm => {
                // Unwrap a << bor_imm(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << bor(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iconst(typeof_x, y);
                    let a = pos.func.dfg.replace(inst).bor(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::BorNot => {
                // Unwrap a << bor_not(x, y)
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
                // Results handled by a << bor(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().bnot(y);
                    let a = pos.func.dfg.replace(inst).bor(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::BxorImm => {
                // Unwrap a << bxor_imm(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << bxor(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iconst(typeof_x, y);
                    let a = pos.func.dfg.replace(inst).bxor(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::BxorNot => {
                // Unwrap a << bxor_not(x, y)
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
                // Results handled by a << bxor(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().bnot(y);
                    let a = pos.func.dfg.replace(inst).bxor(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Fabs => {
                // Unwrap a << fabs.f32(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::F32
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << band_not(x, b).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let b = pos.ins().f32const(ir::immediates::Ieee32::with_bits(0x80000000));
                    let a = pos.func.dfg.replace(inst).band_not(x, b);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << fabs.f64(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::F64
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << band_not(x, b).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let b = pos.ins().f64const(ir::immediates::Ieee64::with_bits(0x8000000000000000));
                    let a = pos.func.dfg.replace(inst).band_not(x, b);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Fcopysign => {
                // Unwrap a << fcopysign.f32(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::Binary {
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        func.dfg.value_type(args[0]) == ir::types::F32
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << bor(a1, a2).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let b = pos.ins().f32const(ir::immediates::Ieee32::with_bits(0x80000000));
                    let a1 = pos.ins().band_not(x, b);
                    let a2 = pos.ins().band(y, b);
                    let a = pos.func.dfg.replace(inst).bor(a1, a2);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << fcopysign.f64(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::Binary {
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        func.dfg.value_type(args[0]) == ir::types::F64
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << bor(a1, a2).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let b = pos.ins().f64const(ir::immediates::Ieee64::with_bits(0x8000000000000000));
                    let a1 = pos.ins().band_not(x, b);
                    let a2 = pos.ins().band(y, b);
                    let a = pos.func.dfg.replace(inst).bor(a1, a2);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::FcvtFromSint => {
                // Unwrap a << fcvt_from_sint.f32.i8(b)
                let (b, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I8 && func.dfg.ctrl_typevar(inst) == ir::types::F32
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << fcvt_from_sint.f32(x).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).fcvt_from_sint(ir::types::F32, x);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << fcvt_from_sint.f32.i16(b)
                let (b, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I16 && func.dfg.ctrl_typevar(inst) == ir::types::F32
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << fcvt_from_sint.f32(x).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).fcvt_from_sint(ir::types::F32, x);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << fcvt_from_sint.f64.i8(b)
                let (b, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I8 && func.dfg.ctrl_typevar(inst) == ir::types::F64
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << fcvt_from_sint.f64(x).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).fcvt_from_sint(ir::types::F64, x);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << fcvt_from_sint.f64.i16(b)
                let (b, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I16 && func.dfg.ctrl_typevar(inst) == ir::types::F64
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << fcvt_from_sint.f64(x).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).fcvt_from_sint(ir::types::F64, x);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Fneg => {
                // Unwrap a << fneg.f32(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::F32
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << bxor(x, b).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let b = pos.ins().f32const(ir::immediates::Ieee32::with_bits(0x80000000));
                    let a = pos.func.dfg.replace(inst).bxor(x, b);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << fneg.f64(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::F64
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << bxor(x, b).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let b = pos.ins().f64const(ir::immediates::Ieee64::with_bits(0x8000000000000000));
                    let a = pos.func.dfg.replace(inst).bxor(x, b);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::IaddCarry => {
                // Unwrap (a, c) << iadd_carry(x, y, c_in)
                let (x, y, c_in, predicate) = if let crate::ir::InstructionData::Ternary {
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        func.dfg.resolve_aliases(args[2]),
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                let a;
                let c;
                {
                    let r = pos.func.dfg.inst_results(inst);
                    a = r[0];
                    c = r[1];
                }
                if predicate {
                    pos.func.dfg.clear_results(inst);
                    let (a1, c1) = pos.ins().iadd_cout(x, y);
                    let c_int = pos.ins().bint(typeof_x, c_in);
                    let (a, c2) = pos.ins().with_results([Some(a), None]).iadd_cout(a1, c_int);
                    let c = pos.ins().with_result(c).bor(c1, c2);
                    let removed = pos.remove_inst();
                    debug_assert_eq!(removed, inst);
                    return true;
                }
            }

            ir::Opcode::IaddCin => {
                // Unwrap a << iadd_cin(x, y, c)
                let (x, y, c, predicate) = if let crate::ir::InstructionData::Ternary {
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        func.dfg.resolve_aliases(args[2]),
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << iadd(a1, c_int).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iadd(x, y);
                    let c_int = pos.ins().bint(typeof_x, c);
                    let a = pos.func.dfg.replace(inst).iadd(a1, c_int);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::IaddCout => {
                // Unwrap (a, c) << iadd_cout(x, y)
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
                let a;
                let c;
                {
                    let r = pos.func.dfg.inst_results(inst);
                    a = r[0];
                    c = r[1];
                }
                if predicate {
                    pos.func.dfg.clear_results(inst);
                    let a = pos.ins().with_result(a).iadd(x, y);
                    let c = pos.ins().with_result(c).icmp(ir::condcodes::IntCC::UnsignedLessThan, a, x);
                    let removed = pos.remove_inst();
                    debug_assert_eq!(removed, inst);
                    return true;
                }
            }

            ir::Opcode::IaddImm => {
                // Unwrap a << iadd_imm(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << iadd(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iconst(typeof_x, y);
                    let a = pos.func.dfg.replace(inst).iadd(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::IcmpImm => {
                // Unwrap a << icmp_imm(cc, x, y)
                let (cc, x, y, predicate) = if let crate::ir::InstructionData::IntCompareImm {
                    cond,
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << icmp(cc, x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iconst(typeof_x, y);
                    let a = pos.func.dfg.replace(inst).icmp(cc, x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::IfcmpImm => {
                // Unwrap a << ifcmp_imm(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << ifcmp(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iconst(typeof_x, y);
                    let a = pos.func.dfg.replace(inst).ifcmp(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::ImulImm => {
                // Unwrap a << imul_imm(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << imul(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iconst(typeof_x, y);
                    let a = pos.func.dfg.replace(inst).imul(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::IrsubImm => {
                // Unwrap a << irsub_imm(y, x)
                let (y, x, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_y = pos.func.dfg.value_type(y);
                // Results handled by a << isub(a1, y).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iconst(typeof_y, x);
                    let a = pos.func.dfg.replace(inst).isub(a1, y);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::IshlImm => {
                // Unwrap a << ishl_imm(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << ishl(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iconst(ir::types::I32, y);
                    let a = pos.func.dfg.replace(inst).ishl(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::IsubBin => {
                // Unwrap a << isub_bin(x, y, b)
                let (x, y, b, predicate) = if let crate::ir::InstructionData::Ternary {
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        func.dfg.resolve_aliases(args[2]),
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << isub(a1, b_int).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().isub(x, y);
                    let b_int = pos.ins().bint(typeof_x, b);
                    let a = pos.func.dfg.replace(inst).isub(a1, b_int);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::IsubBorrow => {
                // Unwrap (a, b) << isub_borrow(x, y, b_in)
                let (x, y, b_in, predicate) = if let crate::ir::InstructionData::Ternary {
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        func.dfg.resolve_aliases(args[2]),
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                let a;
                let b;
                {
                    let r = pos.func.dfg.inst_results(inst);
                    a = r[0];
                    b = r[1];
                }
                if predicate {
                    pos.func.dfg.clear_results(inst);
                    let (a1, b1) = pos.ins().isub_bout(x, y);
                    let b_int = pos.ins().bint(typeof_x, b_in);
                    let (a, b2) = pos.ins().with_results([Some(a), None]).isub_bout(a1, b_int);
                    let b = pos.ins().with_result(b).bor(b1, b2);
                    let removed = pos.remove_inst();
                    debug_assert_eq!(removed, inst);
                    return true;
                }
            }

            ir::Opcode::IsubBout => {
                // Unwrap (a, b) << isub_bout(x, y)
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
                let a;
                let b;
                {
                    let r = pos.func.dfg.inst_results(inst);
                    a = r[0];
                    b = r[1];
                }
                if predicate {
                    pos.func.dfg.clear_results(inst);
                    let a = pos.ins().with_result(a).isub(x, y);
                    let b = pos.ins().with_result(b).icmp(ir::condcodes::IntCC::UnsignedGreaterThan, a, x);
                    let removed = pos.remove_inst();
                    debug_assert_eq!(removed, inst);
                    return true;
                }
            }

            ir::Opcode::RotlImm => {
                // Unwrap a << rotl_imm(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << rotl(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iconst(ir::types::I32, y);
                    let a = pos.func.dfg.replace(inst).rotl(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::RotrImm => {
                // Unwrap a << rotr_imm(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << rotr(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iconst(ir::types::I32, y);
                    let a = pos.func.dfg.replace(inst).rotr(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::SdivImm => {
                // Unwrap a << sdiv_imm(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << sdiv(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iconst(typeof_x, y);
                    let a = pos.func.dfg.replace(inst).sdiv(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::SremImm => {
                // Unwrap a << srem_imm(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << srem(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iconst(typeof_x, y);
                    let a = pos.func.dfg.replace(inst).srem(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::SshrImm => {
                // Unwrap a << sshr_imm(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << sshr(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iconst(ir::types::I32, y);
                    let a = pos.func.dfg.replace(inst).sshr(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::UdivImm => {
                // Unwrap a << udiv_imm(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << udiv(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iconst(typeof_x, y);
                    let a = pos.func.dfg.replace(inst).udiv(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::UremImm => {
                // Unwrap a << urem_imm(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << urem(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iconst(typeof_x, y);
                    let a = pos.func.dfg.replace(inst).urem(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::UshrImm => {
                // Unwrap a << ushr_imm(x, y)
                let (x, y, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << ushr(x, a1).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().iconst(ir::types::I32, y);
                    let a = pos.func.dfg.replace(inst).ushr(x, a1);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::BrIcmp => {
                expand_br_icmp(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::BrTable => {
                expand_br_table(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::Call => {
                expand_call(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::F32const => {
                expand_fconst(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::F64const => {
                expand_fconst(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::GlobalValue => {
                expand_global_value(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::HeapAddr => {
                expand_heap_addr(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::Select => {
                expand_select(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::StackLoad => {
                expand_stack_load(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::StackStore => {
                expand_stack_store(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::TableAddr => {
                expand_table_addr(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::Trapnz => {
                expand_cond_trap(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::Trapz => {
                expand_cond_trap(inst, pos.func, cfg, isa);
                return true;
            }

            _ => {},
        }
    }
    false
}

/// Instruction expansions for architectures with flags.
///
/// Expand some instructions using CPU flags, then fall back to the normal
/// expansions. Not all architectures support CPU flags, so these patterns
/// are kept separate.
#[allow(unused_variables,unused_assignments,non_snake_case)]
pub fn expand_flags(
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
            ir::Opcode::Trapnz => {
                // Unwrap () << trapnz(x, c)
                let (x, c, predicate) = if let crate::ir::InstructionData::CondTrap {
                    code,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        code,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // typeof_x must belong to TypeSet(lanes={1}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[1].contains(typeof_x);
                if predicate {
                    pos.func.dfg.clear_results(inst);
                    let a = pos.ins().ifcmp_imm(x, 0);
                    pos.ins().trapif(ir::condcodes::IntCC::NotEqual, a, c);
                    let removed = pos.remove_inst();
                    debug_assert_eq!(removed, inst);
                    return true;
                }
            }

            ir::Opcode::Trapz => {
                // Unwrap () << trapz(x, c)
                let (x, c, predicate) = if let crate::ir::InstructionData::CondTrap {
                    code,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        code,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // typeof_x must belong to TypeSet(lanes={1}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[1].contains(typeof_x);
                if predicate {
                    pos.func.dfg.clear_results(inst);
                    let a = pos.ins().ifcmp_imm(x, 0);
                    pos.ins().trapif(ir::condcodes::IntCC::Equal, a, c);
                    let removed = pos.remove_inst();
                    debug_assert_eq!(removed, inst);
                    return true;
                }
            }

            _ => {},
        }
    }
    crate::legalizer::expand(inst, pos.func, cfg, isa)
}

/// Legalize instructions by narrowing.
///
/// The transformations in the 'narrow' group work by expressing
/// instructions in terms of smaller types. Operations on vector types are
/// expressed in terms of vector types with fewer lanes, and integer
/// operations are expressed in terms of smaller integer types.
#[allow(unused_variables,unused_assignments,non_snake_case)]
pub fn narrow(
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
            ir::Opcode::Band => {
                // Unwrap a << band(x, y)
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
                // Results handled by a << iconcat(al, ah).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_x must belong to TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[2].contains(typeof_x);
                if predicate {
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (xl, xh) = split::isplit(pos.func, cfg, curpos, srcloc, x);
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (yl, yh) = split::isplit(pos.func, cfg, curpos, srcloc, y);
                    let al = pos.ins().band(xl, yl);
                    let ah = pos.ins().band(xh, yh);
                    let a = pos.func.dfg.replace(inst).iconcat(al, ah);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::BandNot => {
                // Unwrap a << band_not(x, y)
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
                // Results handled by a << iconcat(al, ah).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_x must belong to TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[2].contains(typeof_x);
                if predicate {
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (xl, xh) = split::isplit(pos.func, cfg, curpos, srcloc, x);
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (yl, yh) = split::isplit(pos.func, cfg, curpos, srcloc, y);
                    let al = pos.ins().band_not(xl, yl);
                    let ah = pos.ins().band_not(xh, yh);
                    let a = pos.func.dfg.replace(inst).iconcat(al, ah);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Bnot => {
                // Unwrap a << bnot(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << iconcat(al, ah).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_x must belong to TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[2].contains(typeof_x);
                if predicate {
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (xl, xh) = split::isplit(pos.func, cfg, curpos, srcloc, x);
                    let al = pos.ins().bnot(xl);
                    let ah = pos.ins().bnot(xh);
                    let a = pos.func.dfg.replace(inst).iconcat(al, ah);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Bor => {
                // Unwrap a << bor(x, y)
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
                // Results handled by a << iconcat(al, ah).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_x must belong to TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[2].contains(typeof_x);
                if predicate {
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (xl, xh) = split::isplit(pos.func, cfg, curpos, srcloc, x);
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (yl, yh) = split::isplit(pos.func, cfg, curpos, srcloc, y);
                    let al = pos.ins().bor(xl, yl);
                    let ah = pos.ins().bor(xh, yh);
                    let a = pos.func.dfg.replace(inst).iconcat(al, ah);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::BorNot => {
                // Unwrap a << bor_not(x, y)
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
                // Results handled by a << iconcat(al, ah).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_x must belong to TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[2].contains(typeof_x);
                if predicate {
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (xl, xh) = split::isplit(pos.func, cfg, curpos, srcloc, x);
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (yl, yh) = split::isplit(pos.func, cfg, curpos, srcloc, y);
                    let al = pos.ins().bor_not(xl, yl);
                    let ah = pos.ins().bor_not(xh, yh);
                    let a = pos.func.dfg.replace(inst).iconcat(al, ah);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Brnz => {
                // Unwrap () << brnz.i128(x, ebb1, vararg)
                let (x, ebb1, vararg, predicate) = if let crate::ir::InstructionData::Branch {
                    destination,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = args.as_slice(&func.dfg.value_lists);
                    (
                        func.dfg.resolve_aliases(args[0]),
                        destination,
                        args.iter().skip(2).map(|&arg| func.dfg.resolve_aliases(arg)).collect::<Vec<_>>(),
                        func.dfg.value_type(args[0]) == ir::types::I128
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let vararg = &vararg;
                if predicate {
                    let orig_ebb = pos.current_ebb().unwrap();
                    pos.func.dfg.clear_results(inst);
                    let ebb2 = pos.func.dfg.make_ebb();
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (xl, xh) = split::isplit(pos.func, cfg, curpos, srcloc, x);
                    pos.ins().brnz(xl, ebb1, vararg);
                    pos.ins().jump(ebb2, &[]);
                    pos.insert_ebb(ebb2);
                    pos.ins().brnz(xh, ebb1, vararg);
                    let removed = pos.remove_inst();
                    debug_assert_eq!(removed, inst);
                    cfg.recompute_ebb(pos.func, orig_ebb);
                    cfg.recompute_ebb(pos.func, ebb2);
                    return true;
                }
            }

            ir::Opcode::Brz => {
                // Unwrap () << brz.i128(x, ebb, vararg)
                let (x, ebb, vararg, predicate) = if let crate::ir::InstructionData::Branch {
                    destination,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = args.as_slice(&func.dfg.value_lists);
                    (
                        func.dfg.resolve_aliases(args[0]),
                        destination,
                        args.iter().skip(2).map(|&arg| func.dfg.resolve_aliases(arg)).collect::<Vec<_>>(),
                        func.dfg.value_type(args[0]) == ir::types::I128
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let vararg = &vararg;
                if predicate {
                    pos.func.dfg.clear_results(inst);
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (xl, xh) = split::isplit(pos.func, cfg, curpos, srcloc, x);
                    let a = pos.ins().icmp_imm(ir::condcodes::IntCC::Equal, xl, 0);
                    let b = pos.ins().icmp_imm(ir::condcodes::IntCC::Equal, xh, 0);
                    let c = pos.ins().band(a, b);
                    pos.ins().brnz(c, ebb, vararg);
                    let removed = pos.remove_inst();
                    debug_assert_eq!(removed, inst);
                    cfg.recompute_ebb(pos.func, pos.current_ebb().unwrap());
                    return true;
                }
            }

            ir::Opcode::Bxor => {
                // Unwrap a << bxor(x, y)
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
                // Results handled by a << iconcat(al, ah).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_x must belong to TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[2].contains(typeof_x);
                if predicate {
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (xl, xh) = split::isplit(pos.func, cfg, curpos, srcloc, x);
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (yl, yh) = split::isplit(pos.func, cfg, curpos, srcloc, y);
                    let al = pos.ins().bxor(xl, yl);
                    let ah = pos.ins().bxor(xh, yh);
                    let a = pos.func.dfg.replace(inst).iconcat(al, ah);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::BxorNot => {
                // Unwrap a << bxor_not(x, y)
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
                // Results handled by a << iconcat(al, ah).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_x must belong to TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[2].contains(typeof_x);
                if predicate {
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (xl, xh) = split::isplit(pos.func, cfg, curpos, srcloc, x);
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (yl, yh) = split::isplit(pos.func, cfg, curpos, srcloc, y);
                    let al = pos.ins().bxor_not(xl, yl);
                    let ah = pos.ins().bxor_not(xh, yh);
                    let a = pos.func.dfg.replace(inst).iconcat(al, ah);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Select => {
                // Unwrap a << select(c, x, y)
                let (c, x, y, predicate) = if let crate::ir::InstructionData::Ternary {
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        func.dfg.resolve_aliases(args[2]),
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_c = pos.func.dfg.value_type(c);
                let typeof_x = pos.func.dfg.value_type(x);
                // Results handled by a << iconcat(al, ah).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_x must belong to TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[2].contains(typeof_x);
                if predicate {
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (xl, xh) = split::isplit(pos.func, cfg, curpos, srcloc, x);
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (yl, yh) = split::isplit(pos.func, cfg, curpos, srcloc, y);
                    let al = pos.ins().select(c, xl, yl);
                    let ah = pos.ins().select(c, xh, yh);
                    let a = pos.func.dfg.replace(inst).iconcat(al, ah);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Iconst => {
                narrow_iconst(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::Load => {
                narrow_load(inst, pos.func, cfg, isa);
                return true;
            }

            ir::Opcode::Store => {
                narrow_store(inst, pos.func, cfg, isa);
                return true;
            }

            _ => {},
        }
    }
    false
}

/// Narrow instructions for architectures with flags.
///
/// Narrow some instructions using CPU flags, then fall back to the normal
/// legalizations. Not all architectures support CPU flags, so these
/// patterns are kept separate.
#[allow(unused_variables,unused_assignments,non_snake_case)]
pub fn narrow_flags(
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
            ir::Opcode::Iadd => {
                // Unwrap a << iadd(x, y)
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
                // Results handled by a << iconcat(al, ah).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_x must belong to TypeSet(lanes={1}, ints={16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[3].contains(typeof_x);
                if predicate {
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (xl, xh) = split::isplit(pos.func, cfg, curpos, srcloc, x);
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (yl, yh) = split::isplit(pos.func, cfg, curpos, srcloc, y);
                    let (al, c) = pos.ins().iadd_ifcout(xl, yl);
                    let ah = pos.ins().iadd_ifcin(xh, yh, c);
                    let a = pos.func.dfg.replace(inst).iconcat(al, ah);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Isub => {
                // Unwrap a << isub(x, y)
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
                // Results handled by a << iconcat(al, ah).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_x must belong to TypeSet(lanes={1}, ints={16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[3].contains(typeof_x);
                if predicate {
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (xl, xh) = split::isplit(pos.func, cfg, curpos, srcloc, x);
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (yl, yh) = split::isplit(pos.func, cfg, curpos, srcloc, y);
                    let (al, b) = pos.ins().isub_ifbout(xl, yl);
                    let ah = pos.ins().isub_ifbin(xh, yh, b);
                    let a = pos.func.dfg.replace(inst).iconcat(al, ah);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            _ => {},
        }
    }
    crate::legalizer::narrow(inst, pos.func, cfg, isa)
}

/// Narrow instructions for architectures without flags.
///
/// Narrow some instructions avoiding the use of CPU flags, then fall back
/// to the normal legalizations. Not all architectures support CPU flags,
/// so these patterns are kept separate.
#[allow(unused_variables,unused_assignments,non_snake_case)]
pub fn narrow_no_flags(
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
            ir::Opcode::Iadd => {
                // Unwrap a << iadd(x, y)
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
                // Results handled by a << iconcat(al, ah).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_x must belong to TypeSet(lanes={1}, ints={16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[3].contains(typeof_x);
                if predicate {
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (xl, xh) = split::isplit(pos.func, cfg, curpos, srcloc, x);
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (yl, yh) = split::isplit(pos.func, cfg, curpos, srcloc, y);
                    let (al, c) = pos.ins().iadd_cout(xl, yl);
                    let ah = pos.ins().iadd_cin(xh, yh, c);
                    let a = pos.func.dfg.replace(inst).iconcat(al, ah);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Isub => {
                // Unwrap a << isub(x, y)
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
                // Results handled by a << iconcat(al, ah).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_x must belong to TypeSet(lanes={1}, ints={16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[3].contains(typeof_x);
                if predicate {
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (xl, xh) = split::isplit(pos.func, cfg, curpos, srcloc, x);
                    let curpos = pos.position();
                    let srcloc = pos.srcloc();
                    let (yl, yh) = split::isplit(pos.func, cfg, curpos, srcloc, y);
                    let (al, b) = pos.ins().isub_bout(xl, yl);
                    let ah = pos.ins().isub_bin(xh, yh, b);
                    let a = pos.func.dfg.replace(inst).iconcat(al, ah);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            _ => {},
        }
    }
    crate::legalizer::narrow(inst, pos.func, cfg, isa)
}

/// Legalize instructions by widening.
///
/// The transformations in the 'widen' group work by expressing
/// instructions in terms of larger types.
#[allow(unused_variables,unused_assignments,non_snake_case)]
pub fn widen(
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
            ir::Opcode::Band => {
                // Unwrap a << band(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::Binary {
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
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[0].contains(typeof_b);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let y = pos.ins().uextend(ir::types::I32, c);
                    let z = pos.ins().band(x, y);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::BandImm => {
                // Unwrap a << band_imm(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let z = pos.ins().band_imm(x, c);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::BandNot => {
                // Unwrap a << band_not(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::Binary {
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
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                // typeof_b must belong to TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[0].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let y = pos.ins().uextend(ir::types::I32, c);
                    let z = pos.ins().band_not(x, y);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Bint => {
                // Unwrap a << bint(b)
                let (b, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(x).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_a must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_a);
                if predicate {
                    let x = pos.ins().bint(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_a, x);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Bitrev => {
                // Unwrap a << bitrev.i8(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I8
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << bor(c2, c4).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().band_imm(x, 170);
                    let a2 = pos.ins().ushr_imm(a1, 1);
                    let a3 = pos.ins().band_imm(x, 85);
                    let a4 = pos.ins().ishl_imm(a3, 1);
                    let b = pos.ins().bor(a2, a4);
                    let b1 = pos.ins().band_imm(b, 204);
                    let b2 = pos.ins().ushr_imm(b1, 2);
                    let b3 = pos.ins().band_imm(b, 51);
                    let b4 = pos.ins().ishl_imm(b3, 2);
                    let c = pos.ins().bor(b2, b4);
                    let c1 = pos.ins().band_imm(c, 240);
                    let c2 = pos.ins().ushr_imm(c1, 4);
                    let c3 = pos.ins().band_imm(c, 15);
                    let c4 = pos.ins().ishl_imm(c3, 4);
                    let a = pos.func.dfg.replace(inst).bor(c2, c4);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << bitrev.i16(x)
                let (x, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I16
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << bor(d2, d4).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let a1 = pos.ins().band_imm(x, 43690);
                    let a2 = pos.ins().ushr_imm(a1, 1);
                    let a3 = pos.ins().band_imm(x, 21845);
                    let a4 = pos.ins().ishl_imm(a3, 1);
                    let b = pos.ins().bor(a2, a4);
                    let b1 = pos.ins().band_imm(b, 52428);
                    let b2 = pos.ins().ushr_imm(b1, 2);
                    let b3 = pos.ins().band_imm(b, 13107);
                    let b4 = pos.ins().ishl_imm(b3, 2);
                    let c = pos.ins().bor(b2, b4);
                    let c1 = pos.ins().band_imm(c, 61680);
                    let c2 = pos.ins().ushr_imm(c1, 4);
                    let c3 = pos.ins().band_imm(c, 3855);
                    let c4 = pos.ins().ishl_imm(c3, 4);
                    let d = pos.ins().bor(c2, c4);
                    let d1 = pos.ins().band_imm(d, 65280);
                    let d2 = pos.ins().ushr_imm(d1, 8);
                    let d3 = pos.ins().band_imm(d, 255);
                    let d4 = pos.ins().ishl_imm(d3, 8);
                    let a = pos.func.dfg.replace(inst).bor(d2, d4);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Bnot => {
                // Unwrap a << bnot(b)
                let (b, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                // typeof_b must belong to TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[0].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let z = pos.ins().bnot(x);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Bor => {
                // Unwrap a << bor(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::Binary {
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
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                // typeof_b must belong to TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[0].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let y = pos.ins().uextend(ir::types::I32, c);
                    let z = pos.ins().bor(x, y);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::BorImm => {
                // Unwrap a << bor_imm(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let z = pos.ins().bor_imm(x, c);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::BorNot => {
                // Unwrap a << bor_not(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::Binary {
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
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[0].contains(typeof_b);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let y = pos.ins().uextend(ir::types::I32, c);
                    let z = pos.ins().bor_not(x, y);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::BrTable => {
                // Unwrap () << br_table(x, y, z)
                let (x, y, z, predicate) = if let crate::ir::InstructionData::BranchTable {
                    destination,
                    table,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        destination,
                        table,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_x = pos.func.dfg.value_type(x);
                // typeof_x must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_x);
                if predicate {
                    pos.func.dfg.clear_results(inst);
                    let b = pos.ins().uextend(ir::types::I32, x);
                    pos.ins().br_table(b, y, z);
                    let removed = pos.remove_inst();
                    debug_assert_eq!(removed, inst);
                    cfg.recompute_ebb(pos.func, pos.current_ebb().unwrap());
                    return true;
                }
            }

            ir::Opcode::Bxor => {
                // Unwrap a << bxor(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::Binary {
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
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[0].contains(typeof_b);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let y = pos.ins().uextend(ir::types::I32, c);
                    let z = pos.ins().bxor(x, y);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::BxorImm => {
                // Unwrap a << bxor_imm(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let z = pos.ins().bxor_imm(x, c);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::BxorNot => {
                // Unwrap a << bxor_not(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::Binary {
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
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[0].contains(typeof_b);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let y = pos.ins().uextend(ir::types::I32, c);
                    let z = pos.ins().bxor_not(x, y);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Cls => {
                // Unwrap a << cls.i8(b)
                let (b, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I8
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << ireduce.i8(e).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let c = pos.ins().sextend(ir::types::I32, b);
                    let d = pos.ins().cls(c);
                    let e = pos.ins().iadd_imm(d, -24);
                    let a = pos.func.dfg.replace(inst).ireduce(ir::types::I8, e);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << cls.i16(b)
                let (b, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I16
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << ireduce.i16(e).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let c = pos.ins().sextend(ir::types::I32, b);
                    let d = pos.ins().cls(c);
                    let e = pos.ins().iadd_imm(d, -16);
                    let a = pos.func.dfg.replace(inst).ireduce(ir::types::I16, e);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Clz => {
                // Unwrap a << clz.i8(b)
                let (b, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I8
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << ireduce.i8(e).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let c = pos.ins().uextend(ir::types::I32, b);
                    let d = pos.ins().clz(c);
                    let e = pos.ins().iadd_imm(d, -24);
                    let a = pos.func.dfg.replace(inst).ireduce(ir::types::I8, e);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << clz.i16(b)
                let (b, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I16
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << ireduce.i16(e).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let c = pos.ins().uextend(ir::types::I32, b);
                    let d = pos.ins().clz(c);
                    let e = pos.ins().iadd_imm(d, -16);
                    let a = pos.func.dfg.replace(inst).ireduce(ir::types::I16, e);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Ctz => {
                // Unwrap a << ctz.i8(b)
                let (b, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I8
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << ireduce.i8(e).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let c = pos.ins().uextend(ir::types::I32, b);
                    let d = pos.ins().bor_imm(c, 256);
                    let e = pos.ins().ctz(d);
                    let a = pos.func.dfg.replace(inst).ireduce(ir::types::I8, e);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << ctz.i16(b)
                let (b, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I16
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << ireduce.i16(e).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let c = pos.ins().uextend(ir::types::I32, b);
                    let d = pos.ins().bor_imm(c, 65536);
                    let e = pos.ins().ctz(d);
                    let a = pos.func.dfg.replace(inst).ireduce(ir::types::I16, e);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Iadd => {
                // Unwrap a << iadd(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::Binary {
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
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let y = pos.ins().uextend(ir::types::I32, c);
                    let z = pos.ins().iadd(x, y);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::IaddImm => {
                // Unwrap a << iadd_imm(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let z = pos.ins().iadd_imm(x, c);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Icmp => {
                // Unwrap a << icmp(ir::condcodes::IntCC::Equal, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompare {
                    cond,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        predicates::is_equal(cond, ir::condcodes::IntCC::Equal)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp.i32(ir::condcodes::IntCC::Equal, x, y).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[1].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let y = pos.ins().uextend(ir::types::I32, c);
                    let a = pos.func.dfg.replace(inst).icmp(ir::condcodes::IntCC::Equal, x, y);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp(ir::condcodes::IntCC::NotEqual, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompare {
                    cond,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        predicates::is_equal(cond, ir::condcodes::IntCC::NotEqual)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp.i32(ir::condcodes::IntCC::NotEqual, x, y).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[1].contains(typeof_b);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let y = pos.ins().uextend(ir::types::I32, c);
                    let a = pos.func.dfg.replace(inst).icmp(ir::condcodes::IntCC::NotEqual, x, y);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp(ir::condcodes::IntCC::UnsignedGreaterThan, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompare {
                    cond,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        predicates::is_equal(cond, ir::condcodes::IntCC::UnsignedGreaterThan)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp.i32(ir::condcodes::IntCC::UnsignedGreaterThan, x, y).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[1].contains(typeof_b);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let y = pos.ins().uextend(ir::types::I32, c);
                    let a = pos.func.dfg.replace(inst).icmp(ir::condcodes::IntCC::UnsignedGreaterThan, x, y);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp(ir::condcodes::IntCC::UnsignedLessThan, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompare {
                    cond,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        predicates::is_equal(cond, ir::condcodes::IntCC::UnsignedLessThan)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp.i32(ir::condcodes::IntCC::UnsignedLessThan, x, y).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[1].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let y = pos.ins().uextend(ir::types::I32, c);
                    let a = pos.func.dfg.replace(inst).icmp(ir::condcodes::IntCC::UnsignedLessThan, x, y);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp(ir::condcodes::IntCC::UnsignedGreaterThanOrEqual, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompare {
                    cond,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        predicates::is_equal(cond, ir::condcodes::IntCC::UnsignedGreaterThanOrEqual)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp.i32(ir::condcodes::IntCC::UnsignedGreaterThanOrEqual, x, y).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[1].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let y = pos.ins().uextend(ir::types::I32, c);
                    let a = pos.func.dfg.replace(inst).icmp(ir::condcodes::IntCC::UnsignedGreaterThanOrEqual, x, y);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp(ir::condcodes::IntCC::UnsignedLessThanOrEqual, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompare {
                    cond,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        predicates::is_equal(cond, ir::condcodes::IntCC::UnsignedLessThanOrEqual)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp.i32(ir::condcodes::IntCC::UnsignedLessThanOrEqual, x, y).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[1].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let y = pos.ins().uextend(ir::types::I32, c);
                    let a = pos.func.dfg.replace(inst).icmp(ir::condcodes::IntCC::UnsignedLessThanOrEqual, x, y);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp(ir::condcodes::IntCC::SignedGreaterThan, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompare {
                    cond,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        predicates::is_equal(cond, ir::condcodes::IntCC::SignedGreaterThan)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp(ir::condcodes::IntCC::SignedGreaterThan, x, y).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[1].contains(typeof_b);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let y = pos.ins().sextend(ir::types::I32, c);
                    let a = pos.func.dfg.replace(inst).icmp(ir::condcodes::IntCC::SignedGreaterThan, x, y);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp(ir::condcodes::IntCC::SignedLessThan, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompare {
                    cond,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        predicates::is_equal(cond, ir::condcodes::IntCC::SignedLessThan)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp(ir::condcodes::IntCC::SignedLessThan, x, y).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[1].contains(typeof_b);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let y = pos.ins().sextend(ir::types::I32, c);
                    let a = pos.func.dfg.replace(inst).icmp(ir::condcodes::IntCC::SignedLessThan, x, y);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp(ir::condcodes::IntCC::SignedGreaterThanOrEqual, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompare {
                    cond,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        predicates::is_equal(cond, ir::condcodes::IntCC::SignedGreaterThanOrEqual)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp(ir::condcodes::IntCC::SignedGreaterThanOrEqual, x, y).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[1].contains(typeof_b);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let y = pos.ins().sextend(ir::types::I32, c);
                    let a = pos.func.dfg.replace(inst).icmp(ir::condcodes::IntCC::SignedGreaterThanOrEqual, x, y);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp(ir::condcodes::IntCC::SignedLessThanOrEqual, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompare {
                    cond,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        predicates::is_equal(cond, ir::condcodes::IntCC::SignedLessThanOrEqual)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp(ir::condcodes::IntCC::SignedLessThanOrEqual, x, y).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32, 64, 128})
                let predicate = predicate && TYPE_SETS[1].contains(typeof_b);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let y = pos.ins().sextend(ir::types::I32, c);
                    let a = pos.func.dfg.replace(inst).icmp(ir::condcodes::IntCC::SignedLessThanOrEqual, x, y);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::IcmpImm => {
                // Unwrap a << icmp_imm(ir::condcodes::IntCC::Equal, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompareImm {
                    cond,
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        predicates::is_equal(cond, ir::condcodes::IntCC::Equal)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp_imm(ir::condcodes::IntCC::Equal, x, c).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).icmp_imm(ir::condcodes::IntCC::Equal, x, c);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp_imm(ir::condcodes::IntCC::NotEqual, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompareImm {
                    cond,
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        predicates::is_equal(cond, ir::condcodes::IntCC::NotEqual)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp_imm(ir::condcodes::IntCC::NotEqual, x, c).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).icmp_imm(ir::condcodes::IntCC::NotEqual, x, c);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp_imm(ir::condcodes::IntCC::UnsignedGreaterThan, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompareImm {
                    cond,
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        predicates::is_equal(cond, ir::condcodes::IntCC::UnsignedGreaterThan)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp_imm(ir::condcodes::IntCC::UnsignedGreaterThan, x, c).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).icmp_imm(ir::condcodes::IntCC::UnsignedGreaterThan, x, c);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp_imm(ir::condcodes::IntCC::UnsignedLessThan, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompareImm {
                    cond,
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        predicates::is_equal(cond, ir::condcodes::IntCC::UnsignedLessThan)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp_imm(ir::condcodes::IntCC::UnsignedLessThan, x, c).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).icmp_imm(ir::condcodes::IntCC::UnsignedLessThan, x, c);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp_imm(ir::condcodes::IntCC::UnsignedGreaterThanOrEqual, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompareImm {
                    cond,
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        predicates::is_equal(cond, ir::condcodes::IntCC::UnsignedGreaterThanOrEqual)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp_imm(ir::condcodes::IntCC::UnsignedGreaterThanOrEqual, x, c).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).icmp_imm(ir::condcodes::IntCC::UnsignedGreaterThanOrEqual, x, c);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp_imm(ir::condcodes::IntCC::UnsignedLessThanOrEqual, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompareImm {
                    cond,
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        predicates::is_equal(cond, ir::condcodes::IntCC::UnsignedLessThanOrEqual)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp_imm(ir::condcodes::IntCC::UnsignedLessThanOrEqual, x, c).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).icmp_imm(ir::condcodes::IntCC::UnsignedLessThanOrEqual, x, c);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp_imm(ir::condcodes::IntCC::SignedGreaterThan, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompareImm {
                    cond,
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        predicates::is_equal(cond, ir::condcodes::IntCC::SignedGreaterThan)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp_imm(ir::condcodes::IntCC::SignedGreaterThan, x, c).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).icmp_imm(ir::condcodes::IntCC::SignedGreaterThan, x, c);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp_imm(ir::condcodes::IntCC::SignedLessThan, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompareImm {
                    cond,
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        predicates::is_equal(cond, ir::condcodes::IntCC::SignedLessThan)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp_imm(ir::condcodes::IntCC::SignedLessThan, x, c).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).icmp_imm(ir::condcodes::IntCC::SignedLessThan, x, c);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp_imm(ir::condcodes::IntCC::SignedGreaterThanOrEqual, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompareImm {
                    cond,
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        predicates::is_equal(cond, ir::condcodes::IntCC::SignedGreaterThanOrEqual)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp_imm(ir::condcodes::IntCC::SignedGreaterThanOrEqual, x, c).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).icmp_imm(ir::condcodes::IntCC::SignedGreaterThanOrEqual, x, c);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << icmp_imm(ir::condcodes::IntCC::SignedLessThanOrEqual, b, c)
                let (_, b, c, predicate) = if let crate::ir::InstructionData::IntCompareImm {
                    cond,
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        cond,
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        predicates::is_equal(cond, ir::condcodes::IntCC::SignedLessThanOrEqual)
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << icmp_imm(ir::condcodes::IntCC::SignedLessThanOrEqual, x, c).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).icmp_imm(ir::condcodes::IntCC::SignedLessThanOrEqual, x, c);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Iconst => {
                // Unwrap a << iconst(b)
                let (b, predicate) = if let crate::ir::InstructionData::UnaryImm {
                    imm,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << ireduce(c).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_a must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_a);
                if predicate {
                    let c = pos.ins().iconst(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_a, c);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Imul => {
                // Unwrap a << imul(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::Binary {
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
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let y = pos.ins().uextend(ir::types::I32, c);
                    let z = pos.ins().imul(x, y);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::ImulImm => {
                // Unwrap a << imul_imm(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let z = pos.ins().imul_imm(x, c);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::IrsubImm => {
                // Unwrap a << irsub_imm(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let z = pos.ins().irsub_imm(x, c);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Ishl => {
                // Unwrap a << ishl(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::Binary {
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
                let typeof_b = pos.func.dfg.value_type(b);
                let typeof_c = pos.func.dfg.value_type(c);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let z = pos.ins().ishl(x, c);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::IshlImm => {
                // Unwrap a << ishl_imm(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let z = pos.ins().ishl_imm(x, c);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Isub => {
                // Unwrap a << isub(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::Binary {
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
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let y = pos.ins().uextend(ir::types::I32, c);
                    let z = pos.ins().isub(x, y);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Load => {
                // Unwrap a << load.i8(flags, ptr, off)
                let (flags, ptr, off, predicate) = if let crate::ir::InstructionData::Load {
                    flags,
                    offset,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        flags,
                        func.dfg.resolve_aliases(args[0]),
                        offset,
                        func.dfg.ctrl_typevar(inst) == ir::types::I8
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_ptr = pos.func.dfg.value_type(ptr);
                // Results handled by a << ireduce(b).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let b = pos.ins().uload8(ir::types::I32, flags, ptr, off);
                    let a = pos.func.dfg.replace(inst).ireduce(ir::types::I8, b);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
                // Unwrap a << load.i16(flags, ptr, off)
                let (flags, ptr, off, predicate) = if let crate::ir::InstructionData::Load {
                    flags,
                    offset,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        flags,
                        func.dfg.resolve_aliases(args[0]),
                        offset,
                        func.dfg.ctrl_typevar(inst) == ir::types::I16
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_ptr = pos.func.dfg.value_type(ptr);
                // Results handled by a << ireduce(b).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let b = pos.ins().uload16(ir::types::I32, flags, ptr, off);
                    let a = pos.func.dfg.replace(inst).ireduce(ir::types::I16, b);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Popcnt => {
                // Unwrap a << popcnt(b)
                let (b, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let z = pos.ins().popcnt(x);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Sdiv => {
                // Unwrap a << sdiv(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::Binary {
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
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let y = pos.ins().sextend(ir::types::I32, c);
                    let z = pos.ins().sdiv(x, y);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::SdivImm => {
                // Unwrap a << sdiv_imm(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let z = pos.ins().sdiv_imm(x, c);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Sextend => {
                // Unwrap a << sextend.i16.i8(b)
                let (b, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I8 && func.dfg.ctrl_typevar(inst) == ir::types::I16
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << ireduce(c).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let c = pos.ins().sextend(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).ireduce(ir::types::I16, c);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Srem => {
                // Unwrap a << srem(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::Binary {
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
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let y = pos.ins().sextend(ir::types::I32, c);
                    let z = pos.ins().srem(x, y);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::SremImm => {
                // Unwrap a << srem_imm(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let z = pos.ins().srem_imm(x, c);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Sshr => {
                // Unwrap a << sshr(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::Binary {
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
                let typeof_b = pos.func.dfg.value_type(b);
                let typeof_c = pos.func.dfg.value_type(c);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let z = pos.ins().sshr(x, c);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::SshrImm => {
                // Unwrap a << sshr_imm(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().sextend(ir::types::I32, b);
                    let z = pos.ins().sshr_imm(x, c);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Store => {
                // Unwrap () << store.i8(flags, a, ptr, off)
                let (flags, a, ptr, off, predicate) = if let crate::ir::InstructionData::Store {
                    flags,
                    offset,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        flags,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        offset,
                        func.dfg.value_type(args[0]) == ir::types::I8
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_ptr = pos.func.dfg.value_type(ptr);
                if predicate {
                    pos.func.dfg.clear_results(inst);
                    let b = pos.ins().uextend(ir::types::I32, a);
                    pos.ins().istore8(flags, b, ptr, off);
                    let removed = pos.remove_inst();
                    debug_assert_eq!(removed, inst);
                    return true;
                }
                // Unwrap () << store.i16(flags, a, ptr, off)
                let (flags, a, ptr, off, predicate) = if let crate::ir::InstructionData::Store {
                    flags,
                    offset,
                    ref args,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    (
                        flags,
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.resolve_aliases(args[1]),
                        offset,
                        func.dfg.value_type(args[0]) == ir::types::I16
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_ptr = pos.func.dfg.value_type(ptr);
                if predicate {
                    pos.func.dfg.clear_results(inst);
                    let b = pos.ins().uextend(ir::types::I32, a);
                    pos.ins().istore16(flags, b, ptr, off);
                    let removed = pos.remove_inst();
                    debug_assert_eq!(removed, inst);
                    return true;
                }
            }

            ir::Opcode::Udiv => {
                // Unwrap a << udiv(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::Binary {
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
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let y = pos.ins().uextend(ir::types::I32, c);
                    let z = pos.ins().udiv(x, y);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::UdivImm => {
                // Unwrap a << udiv_imm(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let z = pos.ins().udiv_imm(x, c);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Uextend => {
                // Unwrap a << uextend.i16.i8(b)
                let (b, predicate) = if let crate::ir::InstructionData::Unary {
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        func.dfg.value_type(args[0]) == ir::types::I8 && func.dfg.ctrl_typevar(inst) == ir::types::I16
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                // Results handled by a << ireduce(c).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                if predicate {
                    let c = pos.ins().uextend(ir::types::I32, b);
                    let a = pos.func.dfg.replace(inst).ireduce(ir::types::I16, c);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Urem => {
                // Unwrap a << urem(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::Binary {
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
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let y = pos.ins().uextend(ir::types::I32, c);
                    let z = pos.ins().urem(x, y);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::UremImm => {
                // Unwrap a << urem_imm(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let z = pos.ins().urem_imm(x, c);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::Ushr => {
                // Unwrap a << ushr(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::Binary {
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
                let typeof_b = pos.func.dfg.value_type(b);
                let typeof_c = pos.func.dfg.value_type(c);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let z = pos.ins().ushr(x, c);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            ir::Opcode::UshrImm => {
                // Unwrap a << ushr_imm(b, c)
                let (b, c, predicate) = if let crate::ir::InstructionData::BinaryImm {
                    imm,
                    arg,
                    ..
                } = pos.func.dfg[inst] {
                    let func = &pos.func;
                    let args = [arg];
                    (
                        func.dfg.resolve_aliases(args[0]),
                        imm,
                        true
                    )
                } else {
                    unreachable!("bad instruction format")
                };
                let typeof_b = pos.func.dfg.value_type(b);
                // Results handled by a << ireduce(z).
                let r = pos.func.dfg.inst_results(inst);
                let a = &r[0];
                let typeof_a = pos.func.dfg.value_type(*a);
                // typeof_b must belong to TypeSet(lanes={1}, ints={8, 16, 32})
                let predicate = predicate && TYPE_SETS[4].contains(typeof_b);
                if predicate {
                    let x = pos.ins().uextend(ir::types::I32, b);
                    let z = pos.ins().ushr_imm(x, c);
                    let a = pos.func.dfg.replace(inst).ireduce(typeof_b, z);
                    if pos.current_inst() == Some(inst) {
                        pos.next_inst();
                    }
                    return true;
                }
            }

            _ => {},
        }
    }
    false
}

// Table of value type sets.
const TYPE_SETS: [ir::instructions::ValueTypeSet; 5] = [
    ir::instructions::ValueTypeSet {
        // TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={8, 16, 32, 64, 128})
        lanes: BitSet::<u16>(511),
        ints: BitSet::<u8>(248),
        floats: BitSet::<u8>(0),
        bools: BitSet::<u8>(0),
        refs: BitSet::<u8>(0),
    },
    ir::instructions::ValueTypeSet {
        // TypeSet(lanes={1}, ints={8, 16, 32, 64, 128})
        lanes: BitSet::<u16>(1),
        ints: BitSet::<u8>(248),
        floats: BitSet::<u8>(0),
        bools: BitSet::<u8>(0),
        refs: BitSet::<u8>(0),
    },
    ir::instructions::ValueTypeSet {
        // TypeSet(lanes={1, 2, 4, 8, 16, 32, 64, 128, 256}, ints={16, 32, 64, 128})
        lanes: BitSet::<u16>(511),
        ints: BitSet::<u8>(240),
        floats: BitSet::<u8>(0),
        bools: BitSet::<u8>(0),
        refs: BitSet::<u8>(0),
    },
    ir::instructions::ValueTypeSet {
        // TypeSet(lanes={1}, ints={16, 32, 64, 128})
        lanes: BitSet::<u16>(1),
        ints: BitSet::<u8>(240),
        floats: BitSet::<u8>(0),
        bools: BitSet::<u8>(0),
        refs: BitSet::<u8>(0),
    },
    ir::instructions::ValueTypeSet {
        // TypeSet(lanes={1}, ints={8, 16, 32})
        lanes: BitSet::<u16>(1),
        ints: BitSet::<u8>(56),
        floats: BitSet::<u8>(0),
        bools: BitSet::<u8>(0),
        refs: BitSet::<u8>(0),
    },
];
