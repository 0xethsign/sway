use crate::ops::forc_deploy;
use anyhow::{bail, Result};
use clap::Parser;

/// Deploy contract project.
/// Crafts a contract deployment transaction then sends it to a running node.
#[derive(Debug, Default, Parser)]
pub struct Command {
    /// Path to the project, if not specified, current working directory will be used.
    #[clap(short, long)]
    pub path: Option<String>,
    /// Whether to compile using the original (pre- IR) pipeline.
    #[clap(long, hide = true)]
    pub use_orig_asm: bool,
    /// Whether to compile to bytecode (false) or to print out the generated ASM (true).
    #[clap(long)]
    pub print_finalized_asm: bool,
    /// Whether to compile to bytecode (false) or to print out the generated ASM (true).
    #[clap(long)]
    pub print_intermediate_asm: bool,
    /// Whether to compile to bytecode (false) or to print out the IR (true).
    #[clap(long)]
    pub print_ir: bool,
    /// If set, outputs a binary file representing the script bytes.
    #[clap(short = 'o')]
    pub binary_outfile: Option<String>,
    /// If set, outputs source file mapping in JSON format
    #[clap(short = 'g', long)]
    pub debug_outfile: Option<String>,
    /// Offline mode, prevents Forc from using the network when managing dependencies.
    /// Meaning it will only try to use previously downloaded dependencies.
    #[clap(long = "offline")]
    pub offline_mode: bool,
    /// Silent mode. Don't output any warnings or errors to the command line.
    #[clap(long = "silent", short = 's')]
    pub silent_mode: bool,
    /// The directory in which the sway compiler output artifacts are placed.
    ///
    /// By default, this is `<project-root>/out`.
    #[clap(long)]
    pub output_directory: Option<String>,
    /// By default the JSON for ABIs is formatted for human readability. By using this option JSON
    /// output will be "minified", i.e. all on one line without whitespace.
    #[clap(long)]
    pub minify_json_abi: bool,
    /// Requires that the Forc.lock file is up-to-date. If the lock file is missing, or it
    /// needs to be updated, Forc will exit with an error
    #[clap(long)]
    pub locked: bool,
    /// The node url to deploy, if not specified uses DEFAULT_NODE_URL.
    /// If url is specified overrides network url in manifest file (if there is one).
    #[clap(long, short)]
    pub url: Option<String>,
}

pub(crate) async fn exec(command: Command) -> Result<()> {
    match forc_deploy::deploy(command).await {
        Err(e) => bail!("{}", e),
        _ => Ok(()),
    }
}
