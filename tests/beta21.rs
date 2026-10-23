use std::fs;

use lampe::Project;
use tempfile::tempdir;
use walkdir::WalkDir;

fn extract(source: &str) -> String {
    let dir = tempdir().unwrap();
    fs::write(
        dir.path().join("Nargo.toml"),
        "[package]\nname = \"beta21_literals\"\ntype = \"lib\"\nauthors = []\n",
    )
    .unwrap();
    fs::create_dir(dir.path().join("src")).unwrap();
    fs::write(dir.path().join("src/lib.nr"), source).unwrap();
    Project::new(dir.path().to_owned(), dir.path().to_owned())
        .unwrap()
        .extract(true)
        .unwrap();
    WalkDir::new(dir.path())
        .into_iter()
        .map(Result::unwrap)
        .filter(|entry| entry.path().extension().is_some_and(|ext| ext == "lean"))
        .map(|entry| fs::read_to_string(entry.path()).unwrap())
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn beta21_literals_preserve_signed_values_and_bytes() {
    let output = extract(include_str!("fixtures/beta21_literals.nr"));
    assert!(output.contains("(-9223372036854775808: i64)"), "{output}");
    assert!(output.contains("(-7:"), "{output}");
    assert!(output.contains("340282366920938463463374607431768211455"), "{output}");
    assert!(output.contains("identity<(0 - 7): i32>"), "{output}");
    assert!(output.contains("#_arrayAsStrUnchecked"), "{output}");
    assert!(output.contains("Array<u8, 2: u32>"), "{output}");
    assert!(!output.contains("Array<2: u32,"), "{output}");
    assert!(output.contains("(65: u8), (255: u8), (66: u8)"), "{output}");
    assert!(output.contains("(195: u8), (169: u8)"), "{output}");
    assert!(output.contains("(34: u8), (92: u8), (10: u8)"), "{output}");
}

#[test]
#[should_panic(expected = "Inclusive for loops are not currently supported")]
fn rejects_inclusive_loop_instead_of_dropping_last_iteration() {
    extract("pub fn main() { for i in 0..=1 { assert(i < 2); } }");
}
