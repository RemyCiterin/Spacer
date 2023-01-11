{ stdenv, lib, ocaml, findlib, zarith, num, z3 }:

if lib.versionOlder ocaml.version "4.07"
then throw "z3 is not available for OCaml ${ocaml.version}"
else

let z3-with-ocaml = (z3.override {
  ocamlBindings = true;
  inherit ocaml findlib zarith;
}).overrideAttrs (old: {
    buildInputs = old.buildInputs ++ [ num ];
}); in

stdenv.mkDerivation {

  pname = "ocaml${ocaml.version}-z3";
  inherit (z3-with-ocaml) version;

  dontUnpack = true;

  installPhase = ''
    runHook preInstall
    mkdir -p $OCAMLFIND_DESTDIR
    cp -r ${z3-with-ocaml.ocaml}/lib/ocaml/${ocaml.version}/site-lib/stublibs $OCAMLFIND_DESTDIR
    cp -r ${z3-with-ocaml.ocaml}/lib/ocaml/${ocaml.version}/site-lib/Z3 $OCAMLFIND_DESTDIR/z3
    runHook postInstall
  '';

  nativeBuildInputs = [ findlib ];
  propagatedBuildInputs = [ zarith num ];

  strictDeps = false;

  meta = z3.meta // {
    description = "Z3 Theorem Prover (OCaml API)";
  };
}
