(lang dune 3.7)

(generate_opam_files true)

(license MIT)

(authors "Vadim Yakshigulov <vadim.iakshigulov@gmail.com>")

(maintainers "Vadim Yakshigulov <vadim.iakshigulov@gmail.com>")

(package
 (name Lambada)
 (synopsis "Step-by-step Lambda calculus interpeter")
 (description "With small-step semantic for CBV, CBN, NOR, AO strategies")
 (version 0.1.0)
 (depends
  dune
  angstrom
  (ppx_inline_test :with-test)
  ppx_expect
  ppx_deriving
  ppx_variants_conv
  bisect_ppx
  (odoc :with-doc)
  (ocamlformat :build)
  base))
