extern crate rustc_version;

use rustc_version::{version, Version};

fn main() {
    if version().unwrap() >= Version::parse("1.24.0").unwrap() {
        println!("cargo:rustc-cfg=feature=\"static_assertions\"");
    }
    if version().unwrap() >= Version::parse("1.27.0-beta").unwrap() {
        println!("cargo:rustc-cfg=feature=\"nonnull_cast\"");
    }
}
