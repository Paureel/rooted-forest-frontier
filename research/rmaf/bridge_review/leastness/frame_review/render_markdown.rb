# One-shot prose render check using the installed Ruby RDoc Markdown renderer.
# This checks visible text from generated HTML; it is not browser layout QA.
require 'rdoc'
require 'rdoc/markdown'
require 'rdoc/markup/to_html'
base = File.dirname(__FILE__)
ARGV.each do |path|
  html = RDoc::Markdown.parse(File.read(path)).accept(RDoc::Markup::ToHtml.new(RDoc::Options.new))
  File.write(File.join(base, File.basename(path) + '.html'), html)
end
