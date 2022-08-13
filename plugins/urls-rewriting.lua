prefix_url = config["prefix_url"]

if not prefix_url then
  Plugin.fail("Missing mandatory field: `prefix_url'")
end

if not Regex.match(prefix_url, "^/(.*)") then
  prefix_url = "/" .. prefix_url
end

if not Regex.match(prefix_url, "(.*)/$") then
  prefix_url = prefix_url .. "/"
end

function prefix_urls (links, attr, prefix_url)
  index, link = next(links)

  while index do
    href = HTML.get_attribute(link, attr)

    if href then
      if Regex.match(href, "^/") then
        href = Regex.replace(href, "^/*", "")
        href = prefix_url .. href
      end

      HTML.set_attribute(link, attr, href)
    end
    index, link = next(links, index)
  end
end

prefix_urls(HTML.select(page, "a"), "href", prefix_url)
prefix_urls(HTML.select(page, "link"), "href", prefix_url)
prefix_urls(HTML.select(page, "img"), "src", prefix_url)
prefix_urls(HTML.select(page, "script"), "src", prefix_url)
prefix_urls(HTML.select(page, "use"), "href", prefix_url)
