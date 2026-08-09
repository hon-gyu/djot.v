---
ai-disclosure: none
---

This is a meta note for the whole project, documenting what I want to achieve beyond djot.

- Djot's rationale mentions "xyz should be simple", e.g. in rationale 3. "Rules for emphasis should be simpler." and in 5. "Rules for what content belongs to a list item should be simple.". This is good for solving the ambiguity problem in CommonMark, but since we are formally verifying djot, we can go beyond this principle and make things more complicated as long as we can _prove_ the correctness of the new rules.
- That being said, compatibility with djot is a non-negotiable requirement. Our implementation should be configurable to make djot a subset of our markup.
- Things I have in mind:
    - in djot, sublist must always be preceded by a blank line. I'd like to make this optional under a configuration flag.
    - bring back setext-style (underlined) headings.
    - djot avoids using doubled characters for strong emphasis. Instead, it uses `_` for emphasis and `*` for strong emphasis. The rationale behind this genuinely makes sense to avoid rules in CommonMark. But I think it's a bit too restrictive, would it be enough to allow doubled characters for strong emphasis as long as the character is different from the character for emphasis (e.g. `__` for strong emphasis and `*` for emphasis)? If so, I'd like to make this configurable as well and djot will be a special case by setting the strong emphasis character to `*` and the emphasis character to `_` .
    - following above, there might exists a general design for inline container to cover everything in djot and our extension.
- We generally agree with djot's decision and I'd like to re-emphasize things we won't extend beyond djot:
    - djot forbids raw HTML, this is good.
    - djot forbids indented code blocks, this is good.
- Things I am still thinking about:
    - link reference