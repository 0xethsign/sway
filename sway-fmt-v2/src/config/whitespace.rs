//! Standard system and editor whitespace configuration options. Advanced whitespace options will be deferred to their corresponding sub-classes.
use serde::{Deserialize, Serialize};

use crate::constants::{DEFAULT_MAX_LINE_WIDTH, DEFAULT_TAB_SPACES};

use super::user_opts::WhitespaceOptions;

/// Whitespace styling preferences.
#[derive(Debug, Copy, Clone)]
pub struct Whitespace {
    /// Maximum width of each line.
    pub max_width: usize,
    /// Use tab characters for indentation, spaces for alignment.
    pub hard_tabs: bool,
    /// Number of spaces per tab.
    pub tab_spaces: usize,
    /// Unix or Windows line endings.
    pub newline_style: NewlineStyle,
    /// How we indent expressions or items.
    pub indent_style: IndentStyle,
}

impl Default for Whitespace {
    fn default() -> Self {
        Self {
            max_width: DEFAULT_MAX_LINE_WIDTH,
            hard_tabs: false,
            tab_spaces: DEFAULT_TAB_SPACES,
            newline_style: NewlineStyle::Auto,
            indent_style: IndentStyle::Block,
        }
    }
}

impl Whitespace {
    pub fn from_opts(opts: &WhitespaceOptions) -> Self {
        let default = Self::default();
        Self {
            max_width: opts.max_width.unwrap_or(default.max_width),
            hard_tabs: opts.hard_tabs.unwrap_or(default.hard_tabs),
            tab_spaces: opts.tab_spaces.unwrap_or(default.tab_spaces),
            newline_style: opts.newline_style.unwrap_or(default.newline_style),
            indent_style: opts.indent_style.unwrap_or(default.indent_style),
        }
    }
}

/// Handling of which OS new-line style should be applied.
#[derive(Serialize, Deserialize, Debug, Copy, Clone)]
pub enum NewlineStyle {
    /// Auto-detect based on the raw source input.
    Auto,
    /// Force CRLF (`\r\n`).
    Windows,
    /// Force CR (`\n).
    Unix,
    /// `\r\n` in Windows, `\n` on other platforms.
    Native,
}

/// Handling of line indentation for expressions or items.
#[derive(Serialize, Deserialize, Debug, Copy, Clone)]
pub enum IndentStyle {
    /// First line on the same line as the opening brace, all lines aligned with
    /// the first line.
    Visual,
    /// First line is on a new line and all lines align with **block** indent.
    Block,
}
