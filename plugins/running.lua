function hsl(h, s, l)
  return 'hsl(' .. JSON.to_string(h) .. ', ' .. JSON.to_string(s) .. '%, ' .. JSON.to_string(l) .. '%)'
end

function kilometer(date, n, run)
  local max_hue = 360
  local nb_colors = 17

  local hue = (n * nb_colors) % max_hue
  local bg = hsl(hue, 40, 50 + 10 * (n % 3))
  local border = hsl(hue, 40, 15)

  return HTML.parse ('<span title="' .. date .. '" class="kilometer '
    .. run .. '" style="border: 1px solid '
    .. border .. '; background: ' .. bg .. '"></span>')
end

containers = HTML.select(page, ".running-container")

index, container = next(containers)

-- This way, we won’t have twice the same page.
n = Sys.random(100)

while index do
  if container then
    total_count = 0
    stats = YAML.from_string(String.trim(HTML.inner_html(container)))
    HTML.replace_content(container, HTML.parse(''))

    i = 1
    while stats[i] do
      max = stats[i]['count']
      date = stats[i]['date']
      race = stats[i]['race']

      total_count = total_count + max

      if not border then
        border = 'silver'
      end

      if race then
        race = "race"
      else
        race = ''
      end

      j = 1
      while j <= max do
        HTML.append_child(container, kilometer(date, n, race))
        j = j + 1
      end

      i = i + 1
      n = n + 1
    end

    HTML.append_child(container, HTML.parse('<p>' .. total_count .. 'km in total.'))
  end

  index, container = next(containers, index)
end
