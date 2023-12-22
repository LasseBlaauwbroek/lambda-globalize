(lang dune 2.8)
(name lambda-globalize)

(generate_opam_files true)

(package
 (name lambda-globalize)
 (synopsis "Calculate a context-sensitive, alpha-equivalence respecting hash of a lambda term")
 (maintainers "Lasse Blaauwbroek")
 (authors "Lasse Blaauwbroek")
 (homepage https://github.com/LasseBlaauwbroek/lambda-globalize)
 (bug_reports https://github.com/LasseBlaauwbroek/lambda-globalize/issues)
 (depends ocaml ppx_deriving ppx_inline_test))
