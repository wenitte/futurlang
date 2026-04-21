#!/usr/bin/env node
// Runs after `npm install -g futurlang` to greet the user.

const dim   = '\x1b[2m';
const bold  = '\x1b[1m';
const cyan  = '\x1b[36m';
const green = '\x1b[32m';
const reset = '\x1b[0m';

console.log(`
${bold}${green}FuturLang installed successfully.${reset}

  ${cyan}fl${reset} <file.fl>            run a .fl file
  ${cyan}fl check${reset} <file.fl>      verify proof structure
  ${cyan}fl build${reset} <file.fl>      compile to Rust / binary
  ${cyan}fl create-app${reset} <name>    scaffold a new FL app

${bold}VS Code Extension${reset}
  Get syntax highlighting, hover docs, and completions:
  ${cyan}https://marketplace.visualstudio.com/items?itemName=WenitteApiou.futurlang${reset}

  Or install directly from VS Code:
    Extensions → search "FuturLang" → Install

${dim}Docs: https://github.com/WenitteApiou/futurlang${reset}
`);
