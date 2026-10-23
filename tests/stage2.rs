use std::fs;

use lampe::Project;
use tempfile::tempdir;

#[test]
fn fresh_packages_use_local_libraries_and_link_transitive_environments() {
    let dir = tempdir().unwrap();
    for (name, deps, source) in [
        ("leaf", "", "pub fn value() -> u32 { 7 }"),
        (
            "middle",
            "leaf = { path = '../leaf' }",
            "pub fn value() -> u32 { leaf::value() }",
        ),
        (
            "root",
            "middle = { path = '../middle' }",
            "pub fn value() -> u32 { middle::value() }",
        ),
    ] {
        let package = dir.path().join(name);
        fs::create_dir_all(package.join("src")).unwrap();
        fs::write(
            package.join("Nargo.toml"),
            format!(
                "[package]\nname = '{name}'\ntype = 'lib'\nauthors = []\n[dependencies]\n{deps}\n"
            ),
        )
        .unwrap();
        fs::write(package.join("src/lib.nr"), source).unwrap();
    }
    let root = dir.path().join("root");
    Project::new(root.clone(), root.clone())
        .unwrap()
        .extract(true)
        .unwrap();
    let generated = root.join("lampe");
    for relative in ["", "deps/middle-0.0.0/lampe", "deps/leaf-0.0.0/lampe"] {
        let manifest = fs::read_to_string(generated.join(relative).join("lakefile.toml")).unwrap();
        assert!(!manifest.contains("git ="), "{manifest}");
        assert!(
            manifest.contains(concat!(env!("CARGO_MANIFEST_DIR"), "/Lampe")),
            "{manifest}"
        );
        assert!(manifest.contains("std-1.0.0-beta.21"), "{manifest}");
    }
    let middle_env =
        fs::read_to_string(generated.join("deps/middle-0.0.0/lampe/middle-0.0.0/Extracted.lean"))
            .unwrap();
    assert!(middle_env.contains("++ «leaf-0.0.0».env"), "{middle_env}");
}
