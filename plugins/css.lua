style = HTML.select_one(page, "style")

if style then
  css = HTML.create_text(Sys.read_file("style.min.css"))
  HTML.replace_content(style, css)
end
