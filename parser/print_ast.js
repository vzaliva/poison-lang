const Parser = require("tree-sitter");
const Poison = require("./bindings/node"); // loads your compiled parser

const fs = require("fs");

const parser = new Parser();
parser.setLanguage(Poison.language);

const sourceCode = fs.readFileSync(process.argv[2], "utf8");
const tree = parser.parse(sourceCode);

function nodeToJSON(node) {
  return {
    type: node.type,
    startPosition: node.startPosition,
    endPosition: node.endPosition,
    text: node.text,
    children: node.namedChildren.map(nodeToJSON),
  };
}

console.log(JSON.stringify(nodeToJSON(tree.rootNode), null, 2));
