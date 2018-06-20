extern crate rustc_version;

use rustc_version::{version, Version};

fn main() {
    if version().unwrap() >= Version::parse("1.27.0-beta").unwrap() {
        println!("cargo:rustc-cfg=feature=\"nonnull_cast\"");
        println!("cargo:rustc-cfg=feature=\"global_alloc27\"");
    }
    if version().unwrap() >= Version::parse("1.28.0-alpha").unwrap() {
        println!("cargo:rustc-cfg=feature=\"global_alloc\"");
    } else {
        // We use pre-global-alloc unstable features for rust < 1.28.
        println!("cargo:rustc-env=RUSTC_BOOTSTRAP=1");
    }
}
