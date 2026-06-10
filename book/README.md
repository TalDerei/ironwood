# Ironwood Book

This is the source for the Ironwood book.

## Development

You can render locally and test using `mdbook serve`. Ensure you have installed

* `mdbook v0.4.52`
* `mdbook-katex v0.9.4`
* `mdbook-mermaid v0.16.2`
* `mdbook-admonish v1.20.0`
* (optional) `mdbookkit v1.1.1` (for `mdbook-rustdoc-link`)
    * This renders links to the Ironwood documentation from within the book.
    * Must be enabled by uncommenting `[preprocessor.rustdoc-link] after = ["links"]` in `book.toml`.
    * This requires the `rust-analyzer` component to be installed in your local toolchain.
    * This is expensive to perform re-renders with; try not to use this in
      `mdbook serve` mode until you need to test your documentation links resolve properly.

Pages can be marked as in-progress by adding `<!-- todo -->` to their line in
`src/SUMMARY.md`, which renders a badge in the sidebar.

## Publication

The `main` branch of this repository, when modified, triggers a GitHub Actions
workflow that builds the book and deploys it to GitHub Pages.
