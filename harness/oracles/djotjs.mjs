// djot.js oracle: djot on stdin, HTML on stdout.
// Requires the submodule to be built (make oracles).
import fs from "node:fs";
import { parse, renderHTML } from "../../djot.js/lib/index.js";

const input = fs.readFileSync(0, "utf8");
const warn = () => {};
process.stdout.write(renderHTML(parse(input, { warn }), { warn }));
