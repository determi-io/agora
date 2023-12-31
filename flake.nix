{
  description = "A very basic flake";

  ###################################################
  inputs =
  {
    # base imports
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";

    # determi
    agda-driver.url = "github:determi-io/agda-driver";

    # library deps
    agda-stdlib.url = "github:determi-io/agda-stdlib";

  };

  ###################################################
  outputs = { self, nixpkgs, flake-utils, agda-driver, agda-stdlib }:
  (
    let mkOutputs = system:
    (
      let pkgs = import nixpkgs { inherit system; };
          agda-driver-bin = "${agda-driver.defaultPackage.${system}}/bin/agda-driver";
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [ pkgs.agda ];
          # driver = agda-driver-bin;
          # myoutpath = self.outPath;

          # DETERMI_NIX_AGDA_PATH = "${agda.outputs.packages.x86_64-linux.Agda}/bin/agda";
        };

        packages.default = derivation {
          name = "determi-io-agora";
          builder = agda-driver-bin;
          args = [ ./src ];
          inherit system;

          AGDA_INCLUDES = "${agda-stdlib.packages.${system}.default}/src";

          BLA = "";
        };

        # pkgs.stdenv.mkDerivation {
        #   inherit system;
        #   name = "simple";
        #   builder = "${pkgs.bash}/bin/bash";
        #   args = [ ./simple_builder.sh ];
        # };

      }
    );

    in flake-utils.lib.eachDefaultSystem mkOutputs
  );

}
