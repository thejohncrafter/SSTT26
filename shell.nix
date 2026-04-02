{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  packages = with pkgs; [
    (agda.withPackages [ agdaPackages.standard-library ])
    texliveFull
  ];
}
