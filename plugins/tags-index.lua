counts = {}
env = {}

function append_entry(entry)
  if entry["tags"] then
    i, tag = next(entry["tags"])

    while i do
      if not counts[tag] then
        env[tag] = {}
        counts[tag] = 1
      else
        counts[tag] = counts[tag] + 1
      end

      env[tag][counts[tag]] = entry

      i, tag = next(entry["tags"], i)
    end

    index, entry = next(site_index, index)
  end
end

Table.iter_values_ordered(append_entry, site_index)

tags = {}
tag_count = 1

function append_template_value (tag, entry_list)
  entry = {}
  entry['name'] = tag
  entry['contents'] = env[tag]
  tags[tag_count] = entry
  tag_count = tag_count + 1
end

Table.iter_ordered(append_template_value, env)

res = {}
res['tags'] = tags

template = Sys.read_file(config["index_template_file"])
rendered_entries = HTML.parse(String.render_template(template, res))

container = HTML.select_one(page, config["index_selector"])
HTML.replace_content(container, rendered_entries)

pages = {}
i = 1
current = res['tags'][i]

page_template = [[
<h1><span class="icon"><svg><use href="/img/icons.svg#tag"></use></svg></span> <code>{{ name }}</code></h2>
<article class="index" id="tags-index">
  {{ html }}
</article>
]]

while current  do
  pages[i] = {}
  pages[i]['page_file'] = Sys.join_path(Sys.dirname(page_file), current['name'] .. ".html")

  template = Sys.read_file("templates/index_archives_full.html")
  current['html'] = String.render_template(template, current)
  page_html = String.render_template(page_template, current)

  pages[i]['page_content'] = page_html

  i = i + 1
  current = res['tags'][i]
end
