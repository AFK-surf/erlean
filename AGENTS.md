# Repository instructions

- Write all repository content in English, including documentation, code comments,
  identifiers, test descriptions, and commit messages, regardless of the language
  used in conversation.
- Target Erlang/OTP 29. Record the exact OTP patch version and compiler options
  for imported artifacts and compatibility tests.
- Keep semantic claims scoped to the implemented feature profile and explicit
  runtime assumptions. Do not equate successful testing with a correctness proof.
- Use `docs/design.md` as the single authoritative design and progress tracker.
  Read its implementation tracker before starting work, and update decisions,
  completed checks, limitations, and next steps at each implementation checkpoint.
- Keep work in reviewable commits and push validated checkpoints to the configured
  remote when working under the project's standing commit-and-push instruction.
