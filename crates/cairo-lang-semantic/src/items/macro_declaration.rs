use std::sync::Arc;

use cairo_lang_defs::ids::{LanguageElementId, LookupItemId, MacroDeclarationId, ModuleItemId};
use cairo_lang_diagnostics::{Diagnostics, Maybe, ToMaybe};
use cairo_lang_syntax::attribute::structured::{Attribute, AttributeListStructurize};
use cairo_lang_syntax::node::ast::ExprPlaceholder;
use cairo_lang_syntax::node::db::SyntaxGroup;
use cairo_lang_syntax::node::kind::SyntaxKind;
use cairo_lang_syntax::node::{SyntaxNode, Terminal, TypedSyntaxNode, ast};
use cairo_lang_utils::ordered_hash_map::OrderedHashMap;
use regex::Regex;

use crate::SemanticDiagnostic;
use crate::db::SemanticGroup;
use crate::diagnostic::{NotFoundItemType, SemanticDiagnostics, SemanticDiagnosticsBuilder};
use crate::expr::inference::InferenceId;
use crate::items::macro_declaration;
use crate::resolve::{Resolver, ResolverData};

struct MacroDeclarationData {
    diagnostics: Diagnostics<SemanticDiagnostic>,
    attributes: Vec<Attribute>,
    resolver_data: Arc<ResolverData>,
    rules: Vec<MacroRuleData>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroRuleData {
    pattern: ast::MacroMatcher,
    pub expansion: ast::ExprBlock,
    placeholders: Vec<Placeholder>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Placeholder {
    name: String,
    kind: PlaceholderKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum PlaceholderKind {
    Identifier,
}

impl PlaceholderKind {
    fn regex(&self) -> &str {
        match self {
            PlaceholderKind::Identifier => r"[a-zA-Z_][a-zA-Z0-9_]*",
        }
    }
}

impl From<ast::MacroRuleParamKind> for PlaceholderKind {
    fn from(kind: ast::MacroRuleParamKind) -> Self {
        match kind {
            ast::MacroRuleParamKind::Identifier(_) => PlaceholderKind::Identifier,
            ast::MacroRuleParamKind::Missing(_) => unreachable!(
                "Missing macro rule param kind, should have been handled by the parser."
            ),
        }
    }
}

fn priv_macro_declaration_data(
    db: &dyn SemanticGroup,
    macro_declaration_id: MacroDeclarationId,
) -> Maybe<MacroDeclarationData> {
    let syntax_db: &dyn SyntaxGroup = db.upcast();
    let mut diagnostics = SemanticDiagnostics::default();

    let module_file_id = macro_declaration_id.module_file_id(db.upcast());
    let macro_declaration_syntax =
        db.module_macro_declaration_by_id(macro_declaration_id)?.to_maybe()?;
    let attributes = macro_declaration_syntax.attributes(syntax_db).structurize(syntax_db);
    let inference_id = InferenceId::LookupItemDeclaration(LookupItemId::ModuleItem(
        ModuleItemId::MacroDeclaration(macro_declaration_id),
    ));
    let mut resolver = Resolver::new(db, module_file_id, inference_id);

    let rules = macro_declaration_syntax
        .rules(syntax_db)
        .elements(syntax_db)
        .into_iter()
        .map(|rule_syntax| macro_rule_data(db, rule_syntax, &mut diagnostics))
        .collect();
    let resolver_data = Arc::new(resolver.data);
    Ok(MacroDeclarationData { diagnostics: diagnostics.build(), attributes, resolver_data, rules })
}

fn macro_rule_data(
    db: &dyn SemanticGroup,
    rule_syntax: ast::MacroRule,
    diagnostics: &mut SemanticDiagnostics,
) -> MacroRuleData {
    let pattern = rule_syntax.lhs(db.upcast());
    let expansion = rule_syntax.rhs(db.upcast());
    let placeholders = extract_placeholders(db.upcast(), &pattern, diagnostics);
    MacroRuleData { pattern, expansion, placeholders }
}

fn extract_placeholders(
    db: &dyn SyntaxGroup,
    pattern: &ast::MacroMatcher,
    diagnostics: &mut SemanticDiagnostics,
) -> Vec<Placeholder> {
    let mut placeholders = Vec::new();
    let macro_rule_elements = match pattern {
        ast::MacroMatcher::Parenthesized(inner) => inner.elements(db),
        ast::MacroMatcher::Braced(inner) => inner.elements(db),
        ast::MacroMatcher::Bracketed(inner) => inner.elements(db),
    };
    for macro_rule_element in macro_rule_elements.elements(db) {
        match macro_rule_element {
            ast::MacroRuleElement::Token(_) => {}
            ast::MacroRuleElement::Param(macro_rule_param) => {
                let name = macro_rule_param.name(db).as_syntax_node().get_text_without_trivia(db);
                let kind = macro_rule_param.kind(db).into();
                placeholders.push(Placeholder { name, kind });
            }
        }
    }
    placeholders
}

pub fn macro_rule_pattern_regex(db: &dyn SemanticGroup, rule: &MacroRuleData) -> Regex {
    let pattern = &rule.pattern;
    let mut regex_pattern = String::from("^");
    let syntax_db: &dyn SyntaxGroup = db.upcast();
    let macro_rule_elements = match pattern {
        ast::MacroMatcher::Parenthesized(inner) => inner.elements(syntax_db),
        ast::MacroMatcher::Braced(inner) => inner.elements(syntax_db),
        ast::MacroMatcher::Bracketed(inner) => inner.elements(syntax_db),
    };
    for macro_rule_element in macro_rule_elements.elements(syntax_db) {
        match macro_rule_element {
            ast::MacroRuleElement::Token(token) => {
                let text = token.as_syntax_node().get_text_without_trivia(syntax_db);
                regex_pattern.push_str(&regex::escape(&text));
            }
            ast::MacroRuleElement::Param(param) => {
                let placeholder_kind: PlaceholderKind = param.kind(syntax_db).into();
                regex_pattern.push_str(&format!(
                    "(?P<{}>{})",
                    param.name(syntax_db).as_syntax_node().get_text_without_trivia(syntax_db),
                    placeholder_kind.regex()
                ));
            }
        }
    }
    regex_pattern.push_str("$");
    // TODO: Handle errors
    Regex::new(&regex_pattern).unwrap()
}

/// An alternative implementation to the regex based match checking.
pub fn is_macro_rule_match(
    db: &dyn SemanticGroup,
    rule: &MacroRuleData,
    input: &ast::TokenTreeNode,
) -> Option<OrderedHashMap<String, String>> {
    let mut captures = OrderedHashMap::default();
    let matcher_elements = match &rule.pattern {
        ast::MacroMatcher::Parenthesized(inner) => {
            inner.elements(db.upcast()).elements(db.upcast())
        }
        ast::MacroMatcher::Braced(inner) => inner.elements(db.upcast()).elements(db.upcast()),
        ast::MacroMatcher::Bracketed(inner) => inner.elements(db.upcast()).elements(db.upcast()),
    };
    let input_elements = extract_token_tree_tokens(db.upcast(), input).elements(db.upcast());
    let mut matcher_iter = matcher_elements.iter();
    let mut input_iter = input_elements.iter();
    while let Some(matcher_element) = matcher_iter.next() {
        match matcher_element {
            ast::MacroRuleElement::Token(matcher_token) => match input_iter.next() {
                Some(input_token) => match input_token {
                    ast::TokenTree::Token(token_tree_leaf) => {
                        if matcher_token.as_syntax_node().get_text(db.upcast())
                            != token_tree_leaf.as_syntax_node().get_text(db.upcast())
                        {
                            return None;
                        }
                    }
                    ast::TokenTree::Subtree(_) => {
                        todo!("Subtrees are not supported yet.")
                    }
                    ast::TokenTree::Missing(_) => unreachable!(),
                },
                None => {
                    return None;
                }
            },
            ast::MacroRuleElement::Param(param) => {
                let placeholder_kind: PlaceholderKind = param.kind(db.upcast()).into();
                let placeholder_name =
                    param.name(db.upcast()).as_syntax_node().get_text_without_trivia(db.upcast());
                match placeholder_kind {
                    PlaceholderKind::Identifier => {
                        match input_iter.next() {
                            Some(ast::TokenTree::Token(token_tree_leaf)) => {
                                match token_tree_leaf.leaf(db.upcast()) {
                                    // TODO: Are keywords allowed as identifiers?
                                    ast::TokenNode::TerminalIdentifier(terminal_identifier) => {
                                        captures.insert(
                                            placeholder_name,
                                            terminal_identifier.text(db.upcast()).to_string(),
                                        );
                                    }
                                    _ => {
                                        return None;
                                    }
                                }
                            }
                            _ => {
                                return None;
                            }
                        };
                    }
                }
            }
        }
    }
    if input_iter.next().is_some() {
        return None;
    }
    Some(captures)
}

/// Traverse the macro expansion and replace the placeholders with the provided values, creates a
/// string representation of the expanded macro.
pub fn expand_macro_rule(
    db: &dyn SemanticGroup,
    rule: &MacroRuleData,
    captures: &OrderedHashMap<String, String>,
) -> String {
    let node = rule.expansion.as_syntax_node();
    let mut res_buffer = String::new();
    expand_macro_rule_ex(db, node, captures, &mut res_buffer);
    res_buffer
}

pub fn expand_macro_rule_ex(
    db: &dyn SemanticGroup,
    node: SyntaxNode,
    captures: &OrderedHashMap<String, String>,
    res_buffer: &mut String,
) {
    let syntax_db = db.upcast();
    if node.kind(syntax_db) == SyntaxKind::ExprPlaceholder {
        let placeholder_node = ExprPlaceholder::from_syntax_node(syntax_db, node.clone());
        let placeholder_name =
            placeholder_node.name(syntax_db).as_syntax_node().get_text_without_trivia(syntax_db);
        if let Some(value) = captures.get(&placeholder_name) {
            res_buffer.push_str(value);
        } else {
            // TODO(Gil): verify in the declaration that all the used placeholders in the expansion
            // are present in the captures.
            panic!("Placeholder not found in captures.");
        }
        return;
    }
    if node.kind(syntax_db).is_terminal() {
        res_buffer.push_str(&node.get_text(syntax_db));
        return;
    }
    for child in db.get_children(node).iter() {
        expand_macro_rule_ex(db, child.clone(), captures, res_buffer);
    }
}

fn extract_token_tree_tokens(
    db: &dyn SyntaxGroup,
    token_tree: &ast::TokenTreeNode,
) -> ast::TokenList {
    match token_tree.subtree(db) {
        ast::WrappedTokenTree::Parenthesized(parenthesized_token_tree) => {
            parenthesized_token_tree.tokens(db)
        }
        ast::WrappedTokenTree::Braced(braced_token_tree) => braced_token_tree.tokens(db),
        ast::WrappedTokenTree::Bracketed(bracketed_token_tree) => bracketed_token_tree.tokens(db),
        ast::WrappedTokenTree::Missing(_) => unreachable!(),
    }
}

/// Query implementation of [crate::db::SemanticGroup::macro_declaration_diagnostics].
pub fn macro_declaration_diagnostics(
    db: &dyn SemanticGroup,
    macro_declaration_id: MacroDeclarationId,
) -> Diagnostics<SemanticDiagnostic> {
    priv_macro_declaration_data(db, macro_declaration_id)
        .map(|data| data.diagnostics)
        .unwrap_or_default()
}

/// Query implementation of [crate::db::SemanticGroup::macro_declaration_attributes].
pub fn macro_declaration_attributes(
    db: &dyn SemanticGroup,
    macro_declaration_id: MacroDeclarationId,
) -> Maybe<Vec<Attribute>> {
    priv_macro_declaration_data(db, macro_declaration_id).map(|data| data.attributes)
}

/// Query implementation of [crate::db::SemanticGroup::macro_declaration_resolver_data].
pub fn macro_declaration_resolver_data(
    db: &dyn SemanticGroup,
    macro_declaration_id: MacroDeclarationId,
) -> Maybe<Arc<ResolverData>> {
    priv_macro_declaration_data(db, macro_declaration_id).map(|data| data.resolver_data)
}

/// Query implementation of [crate::db::SemanticGroup::macro_declaration_rules].
pub fn macro_declaration_rules(
    db: &dyn SemanticGroup,
    macro_declaration_id: MacroDeclarationId,
) -> Maybe<Vec<MacroRuleData>> {
    priv_macro_declaration_data(db, macro_declaration_id).map(|data| data.rules)
}
