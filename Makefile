docs: doc/corrode.pdf doc/driver.pdf

doc/corrode.pdf: src/Language/Rust/Corrode/C.md
	pandoc --from markdown --to latex --variable papersize=letter --variable geometry=margin=1in --output "$@" "$^"

doc/driver.pdf: Main.md
	pandoc --from markdown --to latex --variable papersize=letter --variable geometry=margin=1in --output "$@" "$^"
