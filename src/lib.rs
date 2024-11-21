use cedarwood::Cedar;
use regex::Regex;

/* --------------------------------------------------------------------- */
/// Describes things that can go wrong in the match-domain
#[derive(Debug, thiserror::Error)]
pub enum Error {
  /// Failed to compile a regular expression
  #[error(transparent)]
  RegexError(#[from] regex::Error),
}

/* --------------------------------------------------------------------- */
/// Regular expression for domain or prefix
pub const REGEXP_DOMAIN_OR_PREFIX: &str = r"^([a-zA-Z0-9][a-zA-Z0-9-]*[a-zA-Z0-9]*\.)+([a-zA-Z]{2,}|\*)";

/// Reverse a string
fn reverse_string(text: &str) -> String {
  text.chars().rev().collect::<String>()
}

/* --------------------------------------------------------------------- */
#[derive(Debug, Clone)]
/// A struct representing a prefix-or-suffix matching rule.
/// This struct checks if a domain is contained in a list of prefixes or suffixes with longest match rule.
pub struct DomainMatchingRule {
  /// Prefix Cedar
  prefix_cedar: Cedar,
  /// Suffix Cedar
  suffix_cedar: Cedar,
  /// Prefix dictionary
  prefix_dict: Vec<String>,
  /// Suffix dictionary
  suffix_dict: Vec<String>,
}

/* --------------------------------------------------------------------- */
impl TryFrom<Vec<&str>> for DomainMatchingRule {
  type Error = Error;

  /// Populate the domain matching rule from a list of domains
  fn try_from(domain_list: Vec<&str>) -> Result<Self, Self::Error> {
    DomainMatchingRule::try_from(domain_list.as_slice())
  }
}

impl TryFrom<Vec<String>> for DomainMatchingRule {
  type Error = Error;

  /// Populate the domain matching rule from a list of domains
  fn try_from(domain_list: Vec<String>) -> Result<Self, Self::Error> {
    let domain_list: Vec<&str> = domain_list.iter().map(AsRef::as_ref).collect();
    DomainMatchingRule::try_from(domain_list)
  }
}

impl TryFrom<&[&str]> for DomainMatchingRule {
  type Error = Error;

  /// Populate the domain matching rule from a list of domains
  fn try_from(domain_list: &[&str]) -> Result<Self, Self::Error> {
    let start_with_star = Regex::new(r"^\*\..+")?;
    let end_with_star = Regex::new(r".+\.\*$")?;
    // TODO: currently either one of prefix or suffix match with '*' is supported
    let re = Regex::new(&format!("{}{}{}", r"^", REGEXP_DOMAIN_OR_PREFIX, r"$"))?;
    let dict: Vec<String> = domain_list
      .iter()
      .map(|d| if start_with_star.is_match(d) { &d[2..] } else { d })
      .filter(|x| re.is_match(x) || (x.split('.').count() == 1))
      .map(|y| y.to_ascii_lowercase())
      .collect();
    let prefix_dict: Vec<String> = dict
      .iter()
      .filter(|d| end_with_star.is_match(d))
      .map(|d| d[..d.len() - 2].to_string())
      .collect();
    let suffix_dict: Vec<String> = dict
      .iter()
      .filter(|d| !end_with_star.is_match(d))
      .map(|d| reverse_string(d))
      .collect();

    let prefix_kv: Vec<(&str, i32)> = prefix_dict
      .iter()
      .map(AsRef::as_ref)
      .enumerate()
      .map(|(k, s)| (s, k as i32))
      .collect();
    let mut prefix_cedar = Cedar::new();
    prefix_cedar.build(&prefix_kv);

    let suffix_kv: Vec<(&str, i32)> = suffix_dict
      .iter()
      .map(AsRef::as_ref)
      .enumerate()
      .map(|(k, s)| (s, k as i32))
      .collect();
    let mut suffix_cedar = Cedar::new();
    suffix_cedar.build(&suffix_kv);

    Ok(DomainMatchingRule {
      prefix_cedar,
      suffix_cedar,
      prefix_dict,
      suffix_dict,
    })
  }
}

/* --------------------------------------------------------------------- */
impl DomainMatchingRule {
  /// Check if a domain is contained in the list of suffixes
  pub fn find_suffix_match(&self, domain_name: &str) -> bool {
    let rev_nn = reverse_string(domain_name);
    let matched_items = self
      .suffix_cedar
      .common_prefix_iter(&rev_nn)
      .map(|(x, _)| self.suffix_dict[x as usize].clone());

    let mut matched_as_domain = matched_items.filter(|found| {
      if found.len() == rev_nn.len() {
        true
      } else if let Some(nth) = rev_nn.chars().nth(found.chars().count()) {
        nth.to_string() == "."
      } else {
        false
      }
    });
    matched_as_domain.next().is_some()
  }

  /// Check if a domain is contained in the list of prefixes
  fn find_prefix_match(&self, domain_name: &str) -> bool {
    let matched_items = self
      .prefix_cedar
      .common_prefix_iter(domain_name)
      .map(|(x, _)| self.prefix_dict[x as usize].clone());

    let mut matched_as_domain = matched_items.filter(|found| {
      if let Some(nth) = domain_name.chars().nth(found.chars().count()) {
        nth.to_string() == "."
      } else {
        false
      }
    });
    matched_as_domain.next().is_some()
  }

  /// Check if a domain is contained in the list of prefixes or suffixes
  /// We should note that
  /// - the argument `domain_name` should be in lowercase
  /// - the argument `domain_name` should not contain a leading dot
  pub fn is_matched(&self, domain_name: &str) -> bool {
    if self.find_suffix_match(domain_name) {
      tracing::debug!("[with cw] suffix/exact match found: {}", domain_name);
      return true;
    }

    if self.find_prefix_match(domain_name) {
      tracing::debug!("[with cw] prefix match found: {}", domain_name);
      return true;
    }

    // TODO: other matching patterns

    false
  }
}

/* --------------------------------------------------------------------- */

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn matching_works() {
    let domain_matching_rule = DomainMatchingRule::try_from(vec![
      "www.google.com".to_string(),
      "*.google.com".to_string(),
      "yahoo.co.*".to_string(),
    ])
    .unwrap();

    assert!(domain_matching_rule.is_matched("wwxx.google.com"));
    assert!(domain_matching_rule.is_matched("yahoo.co.jp"));

    assert!(!domain_matching_rule.is_matched("www.yahoo.com"));
    assert!(!domain_matching_rule.is_matched("www.yahoo.co.jp"));
  }

  #[test]
  fn matching_works_regardless_of_dns0x20() {
    let domain_matching_rule = DomainMatchingRule::try_from(vec!["GOOGLE.com".to_string()]).unwrap();

    assert!(domain_matching_rule.is_matched("www.google.com"));

    // input domain name must be in lowercase
    assert!(domain_matching_rule.is_matched("WWW.gOoGlE.COM".to_ascii_lowercase().as_str()));
  }
}
