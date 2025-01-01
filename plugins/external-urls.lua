function mark(name)
  return '&nbsp;<span class="icon"><svg><use href="/img/icons.svg#'
         .. name ..
         '"></use></svg></span>'
end

links = HTML.select(page, "a")

index, link = next(links)

while index do
  href = HTML.get_attribute(link, "href")
  todo = not HTML.get_attribute(link, "marked")

  if href and todo then
    if Regex.match(href, "^https?://github.com") then
      icon = HTML.parse(mark("github"))
      HTML.append_child(link, icon)
    elseif Regex.match(href, "^https?://x.com") then
      icon = HTML.parse(mark("twitter"))
      HTML.append_child(link, icon)
    elseif Regex.match(href, "^https?://www.youtube.com") then
      icon = HTML.parse(mark("youtube"))
      HTML.append_child(link, icon)
    elseif Regex.match(href, "^https?://bsky.app") then
      icon = HTML.parse(mark("bsky"))
      HTML.append_child(link, icon)
    elseif Regex.match(href, "^https?://") then
      icon = HTML.parse(mark("external-link"))
      HTML.append_child(link, icon)
    end

    HTML.set_attribute(link, "marked", "")
  end

  index, link = next(links, index)
end
