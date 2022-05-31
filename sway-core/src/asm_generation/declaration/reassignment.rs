use super::*;
use crate::{
    asm_generation::{
        convert_expression_to_asm, expression::get_contiguous_memory_layout, AsmNamespace,
        RegisterSequencer,
    },
    asm_lang::{VirtualImmediate12, VirtualOp},
    constants::VM_WORD_SIZE,
    semantic_analysis::ast_node::{ProjectionKind, TypedReassignment, TypedStructField},
    type_engine::*,
    type_engine::{resolve_type, TypeInfo},
    TypeArgument,
};
use either::Either;

pub(crate) fn convert_reassignment_to_asm(
    reassignment: &TypedReassignment,
    namespace: &mut AsmNamespace,
    register_sequencer: &mut RegisterSequencer,
) -> CompileResult<Vec<Op>> {
    // 0. evaluate the RHS of the reassignment
    // 1. Find the register that the previous var was stored in
    // 2. move the return register of the RHS into the register in the namespace

    let mut buf = vec![];
    let mut warnings = vec![];
    let mut errors = vec![];
    // step 0
    let return_register = register_sequencer.next();
    let mut rhs = check!(
        convert_expression_to_asm(
            &reassignment.rhs,
            namespace,
            &return_register,
            register_sequencer
        ),
        vec![],
        warnings,
        errors
    );

    buf.append(&mut rhs);

    if reassignment.lhs_indices.is_empty() {
        // step 1
        let var_register = check!(
            namespace.look_up_variable(&reassignment.lhs_base_name),
            return err(warnings, errors),
            warnings,
            errors
        );

        // step 2
        buf.push(Op::register_move_comment(
            var_register.clone(),
            return_register,
            reassignment.lhs_base_name.span().clone(),
            format!(
                "variable {} reassignment",
                reassignment.lhs_base_name.as_str(),
            ),
        ));
    } else {
        // TODO(static span) use spans instead of strings below
        let span = sway_types::span::Span::new(
            "TODO(static span): use Idents instead of Strings".into(),
            0,
            0,
            None,
        )
        .unwrap();
        let mut offset_in_words = 0;
        let mut ty = reassignment.lhs_type;
        let mut ty_span = reassignment.lhs_base_name.span();
        let mut lhs_name_for_error = reassignment.lhs_base_name.to_string();
        let mut lhs_span_for_error = reassignment.lhs_base_name.span().clone();
        for kind in &reassignment.lhs_indices {
            let resolved_type = match resolve_type(ty, ty_span) {
                Ok(resolved_type) => resolved_type,
                Err(error) => {
                    errors.push(CompileError::TypeError(error));
                    return err(warnings, errors);
                }
            };
            match (resolved_type, kind) {
                (
                    TypeInfo::Struct {
                        name: struct_name,
                        fields,
                        ..
                    },
                    ProjectionKind::StructField { name },
                ) => {
                    let fields_for_layout = {
                        fields
                            .iter()
                            .map(|TypedStructField { name, r#type, .. }| {
                                (*r#type, span.clone(), name.clone())
                            })
                            .collect::<Vec<_>>()
                    };
                    let field_layout = check!(
                        get_contiguous_memory_layout(&fields_for_layout[..]),
                        return err(warnings, errors),
                        warnings,
                        errors
                    );
                    let field_offset = check!(
                        field_layout.offset_to_field_name(name, name.span().clone()),
                        return err(warnings, errors),
                        warnings,
                        errors
                    );
                    let field_type_opt = {
                        fields.iter().find_map(
                            |TypedStructField {
                                 name: field_name,
                                 r#type,
                                 ..
                             }| {
                                if name == field_name {
                                    Some(r#type)
                                } else {
                                    None
                                }
                            },
                        )
                    };
                    let field_type = match field_type_opt {
                        Some(field_type) => field_type,
                        None => {
                            errors.push(CompileError::FieldNotFound {
                                field_name: name.clone(),
                                struct_name,
                                available_fields: {
                                    fields
                                        .iter()
                                        .map(|field| field.name.as_str())
                                        .collect::<Vec<_>>()
                                        .join(", ")
                                },
                            });
                            return err(warnings, errors);
                        }
                    };
                    offset_in_words += field_offset;
                    ty = *field_type;
                    ty_span = name.span();
                    lhs_name_for_error.push_str(name.as_str());
                    lhs_span_for_error =
                        sway_types::span::Span::join(lhs_span_for_error, name.span().clone());
                }
                (TypeInfo::Tuple(fields), ProjectionKind::TupleField { index, index_span }) => {
                    let fields_for_layout = {
                        fields
                            .iter()
                            .enumerate()
                            .map(|(index, TypeArgument { type_id, span })| {
                                (*type_id, span.clone(), index)
                            })
                            .collect::<Vec<_>>()
                    };
                    let field_layout = check!(
                        get_contiguous_memory_layout(&fields_for_layout[..]),
                        return err(warnings, errors),
                        warnings,
                        errors
                    );
                    let field_offset = check!(
                        field_layout.offset_to_field_name(index, index_span.clone()),
                        return err(warnings, errors),
                        warnings,
                        errors
                    );
                    let field_type_opt = {
                        fields
                            .get(*index)
                            .map(|TypeArgument { type_id, .. }| type_id)
                    };
                    let field_type = match field_type_opt {
                        Some(field_type) => field_type,
                        None => {
                            errors.push(CompileError::TupleIndexOutOfBounds {
                                index: *index,
                                count: fields.len(),
                                span: sway_types::span::Span::join(
                                    lhs_span_for_error,
                                    index_span.clone(),
                                ),
                            });
                            return err(warnings, errors);
                        }
                    };
                    offset_in_words += field_offset;
                    ty = *field_type;
                    ty_span = index_span;
                    lhs_name_for_error.push_str(&index.to_string());
                    lhs_span_for_error =
                        sway_types::span::Span::join(lhs_span_for_error, index_span.clone());
                }
                (actually, ProjectionKind::StructField { .. }) => {
                    errors.push(CompileError::NotAStruct {
                        name: lhs_name_for_error,
                        span: lhs_span_for_error,
                        actually: actually.friendly_type_str(),
                    });
                    return err(warnings, errors);
                }
                (actually, ProjectionKind::TupleField { .. }) => {
                    errors.push(CompileError::NotATuple {
                        name: lhs_name_for_error,
                        span: lhs_span_for_error,
                        actually: actually.friendly_type_str(),
                    });
                    return err(warnings, errors);
                }
            }
        }
        let ptr = check!(
            namespace.look_up_variable(&reassignment.lhs_base_name),
            return err(warnings, errors),
            warnings,
            errors
        );

        let offset_in_bytes = offset_in_words * VM_WORD_SIZE;
        let offset_in_words =
            match VirtualImmediate12::new(offset_in_words, reassignment.rhs.span.clone()) {
                Ok(o) => o,
                Err(e) => {
                    errors.push(e);
                    return err(warnings, errors);
                }
            };

        // the address to write to is:
        // the register `ptr` (the struct pointer)
        // + the offset in words (imm is in words, the vm multiplies it by 8)

        // if the size of this type is > 1 word, then we use MCP to copy the entire value to
        // the mem address pointed to by the struct.
        let size_of_ty = look_up_type_id(reassignment.rhs.return_type)
            .size_in_words(&reassignment.rhs.span)
            .unwrap_or_else(|e| {
                errors.push(e);
                0
            });
        match size_of_ty {
            0 => (),
            1 => {
                buf.push(Op::write_register_to_memory(
                    ptr.clone(),
                    return_register,
                    offset_in_words,
                    sway_types::Span::join(
                        reassignment.lhs_base_name.span().clone(),
                        reassignment.rhs.span.clone(),
                    ),
                ));
            }
            size => {
                // 0. grab the position of the data in the struct (ptr_start + offset_in_bytes)
                // 1. MCPI current ptr, ret register, size_of_ty

                // 0.
                let addr_of_field = register_sequencer.next();
                buf.push(Op {
                    opcode: Either::Left(VirtualOp::ADDI(
                        addr_of_field.clone(),
                        ptr.clone(),
                        VirtualImmediate12::new_unchecked(
                            offset_in_bytes,
                            "structs can't be this big",
                        ),
                    )),
                    comment: "reassign multiword struct field".into(),
                    owning_span: None,
                });

                // 1.
                buf.push(Op {
                    opcode: Either::Left(VirtualOp::MCPI(
                        addr_of_field,
                        return_register,
                        VirtualImmediate12::new_unchecked(
                            size * VM_WORD_SIZE,
                            "structs fields can't be this big",
                        ),
                    )),
                    comment: Default::default(),
                    owning_span: None,
                });
            }
        }
    }

    ok(buf, warnings, errors)
}
