const fs = require('fs');
const { parseFL } = require('./dist/parser/formal');

const filename = process.argv[2];
const source = fs.readFileSync(filename, 'utf8');
const js = parseFL(source);
console.log("Generated JavaScript:");
console.log(js);
console.log("\nExecuting:");
eval(js);
