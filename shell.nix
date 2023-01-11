with (import <nixpkgs> {});
pkgs.mkShell {
  buildInputs = [
    # z3
    ocaml
    fstar
    z3_4_7
    (import ./ocaml-z3.nix { inherit (pkgs) stdenv lib ocaml; inherit (pkgs.ocamlPackages) findlib zarith num;
    z3 = z3_4_7; })
    # ocamlPackages.z3
    ocamlPackages.batteries
    ocamlPackages.findlib
    ocamlPackages.stdint
    ocamlPackages.ocamlbuild
    ocamlPackages.ppx_deriving
    ocamlPackages.ppx_deriving_yojson
    ocamlPackages.menhir
    ocamlPackages.num
    ocamlPackages.lsp
  ];
}