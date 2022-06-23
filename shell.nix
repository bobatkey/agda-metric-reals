{ pkgs ? import <nixpkgs> { } }:
with pkgs;
mkShell {
  buildInputs = [
    (agda.withPackages (ps: [
      ps.standard-library
    ]))
  ];
}
