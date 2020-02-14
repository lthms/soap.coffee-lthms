site_url = config["site_url"]

if not site_url then
  Log.warning("site_url is not configured, using default")
  site_url = ""
end

if not Regex.match(site_url, "(.*)/$") then
  site_url = site_url .. "/"
end

links = HTML.select(page, "a")

index, link = next(links)

while index do
  href = HTML.get_attribute(link, "href")

  if href then
    -- remove prefix sometimes introduced by org
    href = Regex.replace(href, "^file://", "")

    -- Check if URL starts with a leading "/"
    if Regex.match(href, "^/") then
      -- Remove leading slashes
      href = Regex.replace(href, "^/*", "")
      href = site_url .. href
      HTML.set_attribute(link, "href", href)
    end
  end
  index, link = next(links, index)
end
