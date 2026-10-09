use anyhow::{anyhow, Result};
use wavelet_elab::{Program, TypedVar, UntypedVar};

pub(crate) fn type_program(program: &Program<UntypedVar>) -> Result<Program<TypedVar>> {
    wavelet_elab::infer_program(program).map_err(|error| anyhow!(error))
}
