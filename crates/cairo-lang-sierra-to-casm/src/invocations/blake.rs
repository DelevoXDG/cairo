use cairo_lang_casm::{builder::CasmBuilder, hints::ExternalHint};
use cairo_lang_casm::casm_build_extend;
use cairo_lang_sierra::extensions::blake::BlakeConcreteLibfunc;

use super::{CompiledInvocation, CompiledInvocationBuilder, InvocationError};
use crate::invocations::add_input_variables;

/// Builds instructions for Sierra bool operations.
pub fn build(
    libfunc: &BlakeConcreteLibfunc,
    builder: CompiledInvocationBuilder<'_>,
) -> Result<CompiledInvocation, InvocationError> {
    match libfunc {
        BlakeConcreteLibfunc::Blake2sCompress(_) => build_compress(builder),
    }
}

/// Handles instructions for boolean AND.
fn build_compress(
    builder: CompiledInvocationBuilder<'_>,
) -> Result<CompiledInvocation, InvocationError> {
    let [state, byte_count, message] = builder.try_get_single_cells()?;
    let mut casm_builder = CasmBuilder::default();
    add_input_variables! {casm_builder,
        deref state;
        deref byte_count;
        deref message;
    };
    casm_build_extend! {casm_builder,
        tempvar output;
        hint ExternalHint::Blake2sCompress { state, byte_count, message } into {output};
        ap += 1;
    };
    Ok(builder.build_from_casm_builder(
        casm_builder,
        [("Fallthrough", &[&[output]], None)],
        Default::default(),
    ))
}
