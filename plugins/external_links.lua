links = HTML.select(page, "a")

index, link = next(links)

while index do
  href = HTML.get_attribute(link, "href")

  if href then
    if Regex.match(href, "^https?://github.com") then
      icon = HTML.parse("<i class=\"url-mark fa fa-github\" aria-hidden=\"true\"></i>")
      HTML.append_child(link, icon)
    elseif Regex.match(href, "^https?://") then
      icon = HTML.parse("<i class=\"url-mark fa fa-external-link\" aria-hidden=\"true\"></i>")
      HTML.append_child(link, icon)
    end
  end

  index, link = next(links, index)
end
