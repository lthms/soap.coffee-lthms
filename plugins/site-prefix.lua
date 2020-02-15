function fix_urls (links, attr, prefix_url)
  index, link = next(links)

  while index do
    href = HTML.get_attribute(link, attr)

    if href then
      -- remove prefix sometimes introduced by org
      href = Regex.replace(href, "^file://", "")

      -- Check if URL starts with a leading "/"
      if Regex.match(href, "^/") then
        -- Remove leading slashes
        href = Regex.replace(href, "^/*", "")
        href = prefix_url .. href
        HTML.set_attribute(link, attr, href)
      end
    end
    index, link = next(links, index)
  end
end

prefix_url = config["prefix_url"]

if not prefix_url then
  prefix_url = ""
end

if not Regex.match(prefix_url, "(.*)/$") then
  prefix_url = prefix_url .. "/"
end

fix_urls(HTML.select(page, "a"), "href", prefix_url)
fix_urls(HTML.select(page, "link"), "href", prefix_url)
fix_urls(HTML.select(page, "img"), "src", prefix_url)
fix_urls(HTML.select(page, "script"), "src", prefix_url)