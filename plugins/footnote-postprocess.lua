-- Turn `markdown-it-footnote` output into Tufte-compatible sidenotes.

footnotes = HTML.select(page, ".footnote-ref")

index, footnote = next(footnotes)

while index do
  ahref = HTML.select_one(footnote, "a")
  href = HTML.get_attribute(ahref, "href")
  href = Regex.replace(href, "^\#", "")
  footnote_contents = HTML.select_one(page, "li#" .. href)
  HTML.delete(HTML.select_one(footnote_contents, ".footnote-backref"))

  paragraphs = HTML.select(footnote_contents, "p")
  i, p = next(paragraphs)

  while i do
    HTML.set_tag_name(p, "span")
    HTML.add_class(p, "footnote-p")
    i, p = next(paragraphs, i)
  end

  footnote_contents = HTML.inner_html(footnote_contents)

  label = HTML.create_element("label")
  HTML.add_class(label, "margin-toggle")
  HTML.add_class(label, "sidenote-number")
  HTML.set_attribute(label, "for", href)
  HTML.insert_after(footnote, label)

  input = HTML.create_element("input")
  HTML.add_class(input, "margin-toggle")
  HTML.set_attribute(input, "type", "checkbox")
  HTML.set_attribute(input, "id", href)
  HTML.insert_after(label, input)

  contents_node = HTML.create_element("span")
  HTML.add_class(contents_node, "note")
  HTML.add_class(contents_node, "sidenote")
  HTML.append_child(contents_node, HTML.parse(footnote_contents))
  HTML.insert_after(input, contents_node)

  HTML.delete(footnote)
  index, footnote = next(footnotes, index)
end

HTML.delete(HTML.select_one(page, "hr.footnotes-sep"))
HTML.delete(HTML.select_one(page, "section.footnotes"))
