prefix_url = "/" .. soupault_config['widgets']['urls-rewriting']['prefix_url']

env = {}
current_entry = {}

function append_entry(entry)
  if entry['series_url'] then
    if "out" .. entry['series_url'] == target_file then
      if not entry['series_prev_url'] then
        current_entry = prefix_url .. entry['url']
      end

      env[prefix_url .. entry['url']] = entry
    end
  end
end

if site_index and site_index[1] then
  index = HTML.select_one(page, config['index_selector'])

  if index then
    Table.iter_values_ordered(append_entry, site_index)

    res = {}
    res['entries'] = {}
    res_count = 1

    while current_entry do
      res['entries'][res_count] = env[current_entry]
      res_count = res_count + 1

      current_entry = env[current_entry]['series_next_url']
    end

    template = Sys.read_file(config["index_template_file"])
    rendered_entries = HTML.parse(String.render_template(template, res))

    HTML.replace_content(index, rendered_entries)
  end
end
