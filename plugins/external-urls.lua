function mark(name)
  return '<span class="icon"><svg><use href="/img/icons.svg#'
         .. name ..
         '"></use></svg></span>'
end

links = HTML.select(page, "a")

index, link = next(links)

while index do
  href = HTML.get_attribute(link, "href")

  if href then
    if Regex.match(href, "^https?://github.com") then
      icon = HTML.parse(mark("github"))
      HTML.append_child(link, icon)
    elseif Regex.match(href, "^https?://") then
      icon = HTML.parse(mark("external-link"))
      HTML.append_child(link, icon)
    end
  end

  index, link = next(links, index)
end
