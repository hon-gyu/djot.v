@CLAUDE.local.md

---

- see @.project/ for project context; @.project/project-engineering-lessons.md
  persists across sessions (read before committing to a direction:
  estimating a refactor, proposing a theorem, deciding what djot does).
- comment like `CR: ...` means "code review comment"
- edit-and-rebuild cycles is a trap that makes you think you're making progress when you're not. It can be extremely time-consuming and inefficient. It's a strong anti-pattern to avoid. Switch to rocq-mcp for any proof that is slightly interactive.
- one gotcha of rocq-mcp: rocq-mcp caches sessions by preamble hash, so pass `force_restart` after any rebuild; a stale session answers for the old code without saying so.

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