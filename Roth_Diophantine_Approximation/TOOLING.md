# Isabelle proof tooling for Roth

The Isabelle2026-compatible AutoCorrode `isa26` branch is preserved in the
workspace at `../.tooling/AutoCorrode-isa26/`. Its complete, compressed
source archive is
`../.tooling/AutoCorrode-isa26-fb98e9d.tar.gz`.

- Source repository:
  `/Users/lawrpau/NiceProof/src/AwsArgLlcrtNice/theories/isabelle/AutoCorrode`
- Branch: `isa26`
- Revision: `fb98e9d006db9ebcb4f611a6c02bca370abcfa00`
- Archive SHA-256:
  `b67f5f319a0434d4f0bebd4b6d313482305aa620459f2ff34e3c886c7d4f9cb9`

The archive and extracted copy are ignored by this repository because they
are a temporary external tooling dependency, not part of the proposed AFP
entry. If the extracted copy is lost, recreate it with:

```sh
mkdir -p .tooling/AutoCorrode-isa26
tar -xzf .tooling/AutoCorrode-isa26-fb98e9d.tar.gz \
  -C .tooling/AutoCorrode-isa26
```

The `ir` directory supplies the headless I/R REPL. The `iq` directory
supplies the jEdit plugin. The current Codex session uses I/R through
its local console; an I/R MCP endpoint is not registered in this session.
The workspace also retains `.tooling/isabelle-clean.sh`, which filters
out the obsolete NiceProof component during Isabelle startup and uses
workspace-local heaps. The `HOL-Computational_Algebra` heap needed by I/R
is preserved there too. Start the preserved REPL with:

```sh
/Users/lawrpau/isabelle/AutoCorrode-aws-version/ir/.venv/bin/python \
  .tooling/AutoCorrode-isa26/ir/repl.py \
  --isabelle .tooling/isabelle-clean.sh \
  --session HOL-Computational_Algebra \
  --heaps .tooling/isabelle-user/heaps \
  --no-bash-server --repl-only
```
