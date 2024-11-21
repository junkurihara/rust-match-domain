# rust-match-domain

Double-array trie based domain matcher, written in Rust.

This enables you to check if the given domain name matches the prefix or suffix of the domain name in the trie.

## Usage

```rust
use match_domain::DomainMatchingRule;

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
```

Note that for the `DomainMatchingRule::is_matched(&self, domain_name: &str) -> bool` method:

- the argument `domain_name` should be in lowercase
- the argument `domain_name` should not contain a leading dot
