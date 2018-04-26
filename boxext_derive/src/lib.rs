// Copyright 2018 Mike Hommey
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate proc_macro;

#[macro_use]
extern crate syn;

#[macro_use]
extern crate quote;

use proc_macro::TokenStream;
use syn::{Data, DeriveInput, Fields, WhereClause, WherePredicate};

#[proc_macro_derive(Zero)]
pub fn derive_zero(input: TokenStream) -> TokenStream {
    let input: DeriveInput = syn::parse(input).unwrap();

    let name = input.ident;

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let mut types = vec![];

    match input.data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => for f in &fields.named {
                types.push(&f.ty);
            },
            Fields::Unnamed(ref fields) => for f in &fields.unnamed {
                types.push(&f.ty);
            },
            Fields::Unit => {}
        },
        _ => panic!("Can only derive(Zero) for structs"),
    }

    let mut where_clause = where_clause.cloned().unwrap_or_else(|| WhereClause {
        where_token: Default::default(),
        predicates: Default::default(),
    });
    for t in types {
        let p: WherePredicate = parse_quote! { #t: ::boxext::Zero };
        where_clause.predicates.push(p);
    }

    let expanded = quote! {
        unsafe impl #impl_generics ::boxext::Zero for #name #ty_generics #where_clause {}
    };

    expanded.into()
}
