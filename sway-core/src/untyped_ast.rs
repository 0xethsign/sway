use crate::{
    error::{CompileError, CompileWarning, Warning},
    parse_tree::*,
};

use sway_types::span::Span;

/// A single [AstNode] represents a node in the parse tree. Note that [AstNode]
/// is a recursive type and can contain other [AstNode], thus populating the tree.
#[derive(Debug, Clone)]
pub struct AstNode {
    /// The content of this ast node, which could be any control flow structure or other
    /// basic organizational component.
    pub content: AstNodeContent,
    /// The [span::Span] representing this entire [AstNode].
    pub span: Span,
}

/// Represents the various structures that constitute a Sway program.
#[derive(Debug, Clone)]
pub enum AstNodeContent {
    /// A statement of the form `use foo::bar;` or `use ::foo::bar;`
    UseStatement(UseStatement),
    /// A statement of the form `return foo;`
    ReturnStatement(ReturnStatement),
    /// Any type of declaration, of which there are quite a few. See [Declaration] for more details
    /// on the possible variants.
    Declaration(Declaration),
    /// Any type of expression, of which there are quite a few. See [Expression] for more details.
    Expression(Expression),
    /// An implicit return expression is different from a [AstNodeContent::ReturnStatement] because
    /// it is not a control flow item. Therefore it is a different variant.
    ///
    /// An implicit return expression is an [Expression] at the end of a code block which has no
    /// semicolon, denoting that it is the [Expression] to be returned from that block.
    ImplicitReturnExpression(Expression),
    /// A control flow element which loops continually until some boolean expression evaluates as
    /// `false`.
    WhileLoop(WhileLoop),
    /// A statement of the form `dep foo::bar;` which imports/includes another source file.
    IncludeStatement(IncludeStatement),
}

/// Context for checking that the attributed purity of a function definition matches the actual
/// purity based on the existence or lack of storage operations found within.
///
/// These properties are all set for the function currently being checked.  When recursing into an
/// inlined function definition we create a new `PurityChecker`.
pub struct PurityChecker<'a> {
    fn_sig_span: Option<&'a Span>,
    purity: Purity,
    is_pure: bool,
    pub warnings: Vec<CompileWarning>,
    pub errors: Vec<CompileError>,
}

impl<'a> Default for PurityChecker<'a> {
    fn default() -> Self {
        PurityChecker {
            fn_sig_span: None,
            purity: Purity::Pure,
            is_pure: true,
            warnings: Vec::new(),
            errors: Vec::new(),
        }
    }
}

impl<'a> PurityChecker<'a> {
    fn new(fn_sig_span: &'a Span, purity: Purity) -> Self {
        PurityChecker {
            fn_sig_span: Some(fn_sig_span),
            purity,
            is_pure: true,
            warnings: Vec::new(),
            errors: Vec::new(),
        }
    }

    /// Searches the AST for storage operations and confirms the annotations of associated function
    /// declarations have the correct attributes.
    pub(crate) fn check_purity_astnode(&mut self, node: &AstNode) {
        match &node.content {
            AstNodeContent::Declaration(decl) => self.check_purity_declaration(decl),
            AstNodeContent::ReturnStatement(ret_stmt) => {
                self.check_purity_expression(&ret_stmt.expr)
            }
            AstNodeContent::Expression(expr) | AstNodeContent::ImplicitReturnExpression(expr) => {
                self.check_purity_expression(expr)
            }
            AstNodeContent::WhileLoop(WhileLoop { condition, body }) => {
                self.check_purity_expression(condition);
                self.check_purity_code_block(body);
            }

            AstNodeContent::UseStatement(_) => (),
            AstNodeContent::IncludeStatement(_) => (),
        }
    }

    fn check_purity_declaration(&mut self, decl: &Declaration) {
        match decl {
            Declaration::VariableDeclaration(VariableDeclaration { body, .. }) => {
                self.check_purity_expression(body);
            }
            Declaration::FunctionDeclaration(fn_decl) => {
                self.check_purity_function_declaration(fn_decl);
            }
            Declaration::TraitDeclaration(TraitDeclaration { methods, .. })
            | Declaration::AbiDeclaration(AbiDeclaration { methods, .. }) => {
                for method in methods {
                    self.check_purity_function_declaration(method);
                }
            }
            Declaration::Reassignment(Reassignment { lhs, rhs, .. }) => {
                if let ReassignmentTarget::VariableExpression(expr) = lhs {
                    self.check_purity_expression(expr);
                }
                self.check_purity_expression(rhs);
            }
            Declaration::ImplTrait(ImplTrait { functions, .. })
            | Declaration::ImplSelf(ImplSelf { functions, .. }) => {
                for function in functions {
                    self.check_purity_function_declaration(function);
                }
            }
            Declaration::ConstantDeclaration(ConstantDeclaration { value, .. }) => {
                // The constant decl should just have a literal for a RHS but it's wrapped as an
                // Expression so we should check it.
                self.check_purity_expression(value);
            }

            Declaration::StructDeclaration(_)
            | Declaration::EnumDeclaration(_)
            | Declaration::StorageDeclaration(_) => (),
        }
    }

    fn check_purity_function_declaration(&mut self, fn_decl: &FunctionDeclaration) {
        let FunctionDeclaration {
            purity,
            body,
            sig_span,
            ..
        } = fn_decl;

        let mut checker = PurityChecker::new(sig_span, *purity);
        checker.check_purity_code_block(body);
        self.warnings.append(&mut checker.warnings);
        self.errors.append(&mut checker.errors);

        if checker.purity != Purity::Pure && checker.is_pure {
            self.warnings.push(CompileWarning {
                warning_content: Warning::DeadStorageDeclarationForFunction,
                span: checker.fn_sig_span.cloned().unwrap_or_else(Span::dummy),
            });
        }
    }

    fn check_purity_code_block(&mut self, code_block: &CodeBlock) {
        for node in &code_block.contents {
            self.check_purity_astnode(node);
        }
    }

    fn check_purity_expression(&mut self, expression: &Expression) {
        match expression {
            // The root check for non-pure operations.
            Expression::AsmExpression { asm, .. } => self.check_purity_asm_expression(asm),

            // Recurse for a single sub-expression.
            Expression::TupleIndex { prefix: expr, .. }
            | Expression::SubfieldExpression { prefix: expr, .. }
            | Expression::AbiCast { address: expr, .. }
            | Expression::SizeOfVal { exp: expr, .. } => {
                self.check_purity_expression(expr);
            }

            // Recurse for a pair of sub-expressions.
            Expression::LazyOperator {
                lhs: expr_a,
                rhs: expr_b,
                ..
            }
            | Expression::ArrayIndex {
                prefix: expr_a,
                index: expr_b,
                ..
            } => {
                self.check_purity_expression(expr_a);
                self.check_purity_expression(expr_b);
            }

            // Recurse for a Vec of sub-expressions.
            Expression::FunctionApplication {
                arguments: exprs, ..
            }
            | Expression::Tuple { fields: exprs, .. }
            | Expression::Array {
                contents: exprs, ..
            }
            | Expression::DelineatedPath { args: exprs, .. } => {
                for expr in exprs {
                    self.check_purity_expression(expr);
                }
            }

            Expression::CodeBlock { contents, .. } => self.check_purity_code_block(contents),
            Expression::IfExp {
                condition,
                then,
                r#else,
                ..
            } => {
                self.check_purity_expression(condition);
                self.check_purity_expression(then);
                if let Some(expr) = r#else {
                    self.check_purity_expression(expr);
                }
            }
            Expression::MatchExp {
                value, branches, ..
            } => {
                self.check_purity_expression(value);
                for branch in branches {
                    self.check_purity_expression(&branch.result);
                }
            }
            Expression::MethodApplication {
                contract_call_params,
                arguments,
                ..
            } => {
                for field in contract_call_params {
                    self.check_purity_expression(&field.value);
                }
                for argument in arguments {
                    self.check_purity_expression(argument);
                }
            }

            // No sub-expressions for these variants.
            Expression::Literal { .. }
            | Expression::VariableExpression { .. }
            | Expression::StructExpression { .. }
            | Expression::StorageAccess { .. }
            | Expression::BuiltinGetTypeProperty { .. }
            | Expression::BuiltinGenerateUid { .. } => (),
        }
    }

    fn check_purity_asm_expression(&mut self, asm: &AsmExpression) {
        if self.purity == Purity::ReadsWrites {
            // We can skip the check if we have full privileges already.
            return;
        }

        let (reads, writes) = asm
            .body
            .iter()
            .fold((false, false), |(reads, writes), asm_op| {
                match asm_op.op_name.as_str() {
                    "srw" | "srwq" => (true, writes),
                    "sww" | "swwq" => (reads, true),
                    _ => (reads, writes),
                }
            });

        if reads || writes {
            self.is_pure = false;
        }

        let (storage_op, required_purity) = match (self.purity, reads, writes) {
            (Purity::Pure, true, false) => ("read", Purity::Reads),
            (Purity::Pure, false, true) => ("write", Purity::Writes),
            (Purity::Pure, true, true) => ("read & write", Purity::ReadsWrites),
            (Purity::Reads, _, true) => ("write", Purity::ReadsWrites),
            (Purity::Writes, true, _) => ("read", Purity::ReadsWrites),

            // (Pure, false, false) is OK, and ReadsWrites allows anything.
            _otherwise => return,
        };

        // At this stage we anticipate having a Some(fn_name) and Some(fn_sig_span) since to detect
        // improper purity we must have found offending ASM blocks, which must exist within a
        // function context.

        self.errors.push(CompileError::ImpureInPureContext {
            storage_op,
            attrs: required_purity.to_attribute_syntax(),
            span: self.fn_sig_span.cloned().unwrap_or_else(Span::dummy),
        });
    }
}
