-- Thin client for the editor-independent stdio server. Neovim 0.10+.
local M = {}
local settings = {}
local repo = debug.getinfo(1, 'S').source:sub(2)
for _ = 1, 5 do repo = vim.fs.dirname(repo) end

local legacy = {
  'FibrilFormat', 'FibrilReference', 'FibrilCheckProject', 'FibrilCheck',
  'FibrilDefinitionProject', 'FibrilDefinitionPackage', 'FibrilDefinition',
  'FibrilRenamePreview', 'FibrilReferences',
}

function M.start(bufnr)
  bufnr = bufnr or vim.api.nvim_get_current_buf()
  local filename = vim.api.nvim_buf_get_name(bufnr)
  if filename == '' or vim.bo[bufnr].buftype ~= '' then return end
  local root = settings.root_dir
  if type(root) == 'function' then root = root(filename) end
  root = root or vim.fs.root(filename, '.git')
    or vim.fs.root(filename, 'fibril.yaml') or vim.fs.dirname(filename)
  for _, command in ipairs(legacy) do
    pcall(vim.api.nvim_buf_del_user_command, bufnr, command)
    pcall(vim.keymap.del, 'n', '<Plug>(' .. command .. ')', { buffer = bufnr })
  end
  vim.bo[bufnr].commentstring = '-- %s'
  local capabilities = vim.tbl_deep_extend('force',
    vim.lsp.protocol.make_client_capabilities(), settings.capabilities or {})
  return vim.lsp.start({
    name = 'fibril_lsp',
    cmd = settings.cmd or { settings.python or 'python3', repo .. '/tools/fibril_lsp.py',
      '--fibril', settings.fibril or repo .. '/build/exec/fibril' },
    root_dir = root,
    capabilities = capabilities,
    init_options = settings.init_options or {},
    on_attach = function(client, buffer)
      if settings.keymaps ~= false then
        local maps = {
          gd = { vim.lsp.buf.definition, 'Fibril definition' },
          gr = { vim.lsp.buf.references, 'Fibril references (checked scope)' },
          K = { vim.lsp.buf.hover, 'Fibril documentation' },
          ['<leader>rn'] = { vim.lsp.buf.rename, 'Fibril guarded rename (standalone)' },
          ['<leader>f'] = { function() vim.lsp.buf.format({ bufnr = buffer }) end, 'Fibril format' },
        }
        for key, action in pairs(maps) do
          vim.keymap.set('n', key, action[1], { buffer = buffer, desc = action[2] })
        end
      end
      if settings.on_attach then settings.on_attach(client, buffer) end
    end,
  }, { bufnr = bufnr })
end

function M.setup(options)
  if vim.fn.has('nvim-0.10') == 0 then error('Fibril LSP requires Neovim 0.10+') end
  settings = options or {}
  -- The existing Vim syntax files remain usable, but Neovim no longer installs
  -- their custom compiler-command integration when this LSP client is enabled.
  vim.g.fibril_use_lsp = 1
  vim.opt.runtimepath:append(repo .. '/editors/vim')
  vim.filetype.add({ extension = { fib = 'fibril' } })
  local group = vim.api.nvim_create_augroup('FibrilLsp', { clear = true })
  vim.api.nvim_create_autocmd('FileType', {
    group = group, pattern = 'fibril',
    callback = function(event) M.start(event.buf) end,
  })
  for _, buffer in ipairs(vim.api.nvim_list_bufs()) do
    if vim.api.nvim_buf_is_loaded(buffer) and vim.bo[buffer].filetype == 'fibril' then
      M.start(buffer)
    end
  end
end

return M
