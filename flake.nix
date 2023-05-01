{
  description = "Haskell Flake";
  inputs.nixpkgs.url = "nixpkgs";
  outputs = { self, nixpkgs }:
    let
      supportedSystems = [ "x86_64-linux" "x86_64-darwin" ];
      forAllSystems = f:
        nixpkgs.lib.genAttrs supportedSystems (system: f system);
      nixpkgsFor = forAllSystems (system:
        import nixpkgs {
          inherit system;
          overlays = [ self.overlay ];
        });
    in {
      overlay = (final: prev: {
        haskell-hello =
          final.haskellPackages.callCabal2nix "haskell-hello" ./. { };
      });
      packages = forAllSystems
        (system: { haskell-hello = nixpkgsFor.${system}.haskell-hello; });
      defaultPackage =
        forAllSystems (system: self.packages.${system}.haskell-hello);
      checks = self.packages;
      devShell = forAllSystems (system:
        let
          nixpkgs = nixpkgsFor.${system};
          haskellPackages = nixpkgs.haskellPackages;
        in haskellPackages.shellFor {
          packages = p: [ self.packages.${system}.haskell-hello ];
          withHoogle = true;
          buildInputs = with nixpkgs;
            with haskellPackages; [
              haskell-language-server
              cabal-install
              (agda.withPackages (p: [ p.standard-library ]))
            ];
          # Change the prompt to show that you are in a devShell
          shellHook = "export PS1='\\e[1;34magda > \\e[0m'";
        });
    };
}
