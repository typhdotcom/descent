{
  description = "descent";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    project-utils = {
      url = "git+ssh://git@git.typh.com:2222/typh/project-utils.git";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    {
      self,
      nixpkgs,
      project-utils,
    }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};

      common = project-utils.lib.common { inherit self pkgs; };
    in
    {
      formatter.${system} = common.formatter;

      checks.${system} = common.checks // {
      };

      devShells.${system}.default = pkgs.mkShell {
        packages = [
        ];
      };
    };
}
