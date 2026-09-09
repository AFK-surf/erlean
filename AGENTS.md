# Repository instructions

- Write all repository content in English, including documentation, code comments,
  identifiers, test descriptions, and commit messages, regardless of the language
  used in conversation.
- Keep this upstream repository application-independent. Do not name downstream
  projects or record their designs, pull requests, or implementation progress here.
- Target Erlang/OTP 29. Record the exact OTP patch version and compiler options
  for imported artifacts and compatibility tests.
- Manage OTP installations with asdf and honor the repository `.tool-versions`.
  Missing development dependencies may be installed as needed.
- Keep semantic claims scoped to the implemented feature profile and explicit
  runtime assumptions. Do not equate successful testing with a correctness proof.
- Use `docs/design.md` as the single authoritative design and progress tracker.
  Read its implementation tracker before starting work, and update decisions,
  completed checks, limitations, and next steps at each implementation checkpoint.
- Keep work in reviewable commits and push validated checkpoints to the configured
  remote when working under the project's standing commit-and-push instruction.
- Run builds and verification serially through the primary agent. Use
  `node tools/build.mjs` for dependency-ordered builds with one compilation at a
  time. Do not run overlapping Lake builds or test suites from subagents.
  Lean compiler processes are capped at 2 GiB and one worker thread.
