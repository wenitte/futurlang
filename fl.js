#!/usr/bin/env node
const fs   = require('fs');
const args = process.argv.slice(2);

const ROUTED_COMMANDS = ['setup', 'verify', 'check'];

if (args.length === 0 || ROUTED_COMMANDS.includes(args[0])) {
  require('./dist/cli');
} else {
  const { parseFL } = require('./dist/parser/formal');
  const filename = args[0];
  if (!filename) { console.error('Usage: fl <file.fl>'); process.exit(1); }
  const source = fs.readFileSync(filename, 'utf8');
  const js = parseFL(source);
  try { eval(js); }
  catch(e) { console.error(e.message); process.exit(1); }
}
