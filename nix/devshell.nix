{
  perSystem =
    { pkgs, ... }:
    {
      devShells.default = pkgs.mkShell {
        packages = [
          pkgs.elan
          pkgs.git
          pkgs.curl
          pkgs.nushell
        ];

        # pkgs.elan supplies the lake/lean proxies; ELAN_HOME is only where the
        # toolchain named in ../lean-toolchain gets cached on first use.
        shellHook = ''
          export ELAN_HOME="''${ELAN_HOME:-$HOME/.elan}"
        '';
      };
    };
}
