@CLAUDE.local.md

---

- see @.project/ for project context; @.project/project-engineering-lessons.md
  persists across sessions (read before committing to a direction:
  estimating a refactor, proposing a theorem, deciding what djot does).
- comment like `CR: ...` means "code review comment"
- repetitive edit-and-rebuild cycles can be inefficient, which is an anti-pattern. make use of the interactive mode of rocq-mcp where appropriate.

# AI content disclosure

Some files has "ai-disclosure" tag, which is one of:

| Value          | Meaning                                         |
| -------------- | ----------------------------------------------- |
| `none`         | No AI involvement; a human-only assertion       |
| `ai-assisted`  | Human-authored, AI edited or refined            |
| `ai-generated` | AI-generated with human prompting and/or review |
| `autonomous`   | AI-generated without human oversight            |

- Add appropriate disclosure to the file.
- Be careful about information that lacks human oversight.
- Add trailer at commit message, example:
```
Ai-disclosure: autonomous
Ai-agent: anthropic/claude-opus-5
```