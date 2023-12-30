#!/usr/bin/node

function renderer() {
  return require('markdown-it')()
            .use(require('@ryanxcharles/markdown-it-katex'))
            .use(require('markdown-it-meta'))
            .use(require('markdown-it-footnote'))
            .use(require('markdown-it-figure'))
            .use(require('markdown-it-custom-block'), {
                allSeries (placeholder) {
                  return `<div class="index" id="all-series-index"></div>`
                },
                series (placeholder) {
                  return `<div class="index" id="series-index"></div>`
                },
                tags (placeholder) {
                  return `<div class="index" id="tags-index"></div>`
                },
                archives (placeholder) {
                  if (placeholder == 'all') {
                    return `<div class="index" id="archives-index"></div>`
                  } else {
                    return `<div id="archives-index">${placeholder}</div>`
                  }
                },
                video (url) {
                  return `<video controls><source src="${url}" /></video>`
                }
              })
            .use(require('markdown-it-highlightjs'), { inline: true, auto: false });
}

function icon(name) {
  return `<span class="icon"><svg><use href="/img/icons.svg#${name}"></use></svg></span>`;
}

const fs = require('fs');
const md = renderer();

const path = process.argv[2];

function calendar(date) {
  return `${date.getFullYear()}-${(date.getMonth() + 1).toString().padStart(2, '0')}-${date.getDate().toString().padStart(2, '0')}`;
}

function datetime(date, id) {
  const options = { year: 'numeric', month: 'long', day: 'numeric' };

  return `<time datetime="${calendar(date)}" id="${id}">${date.toLocaleDateString('en-US', options)}</time>`;
}

function span(str, cls) {
  return `<span class="${cls}">${str}</span>`;
}

fs.readFile(path, 'utf8', (err, data) => {
  if (err) {
    process.exit(1);
  }

  const document = md.render(data);
  const series = md.meta.series;
  const published = md.meta.published;
  const modified = md.meta.modified;
  const tags = md.meta.tags;
  const abstract = md.meta.abstract;
  const feature = md.meta.feature;

  process.stdout.write('<div id="meta-tags">');
  if (abstract) {
    const abstract_rendered =  renderer().render(abstract);
    process.stdout.write(`<div class="description">${abstract_rendered}</div>`);
  }
  if (feature) {
    process.stdout.write(`<div class="feature">yes</div>`);
  }
  process.stdout.write('</div>');

  process.stdout.write('<span id="timestamps" class="marginblock">');

  if (published || tags) {
    if (published) {
      process.stdout.write(span(`${icon('clock')}&nbsp;Published on ${datetime(published, 'published')}`, 'footnote-p full-only narrow'));

      if (modified) {
        process.stdout.write(span(`${icon('edit')}&nbsp;Modified on ${datetime(modified, 'modified')}`, 'footnote-p full-only narrow'));
      }
    }
  }

  process.stdout.write('</span>');

  if (series) {
    process.stdout.write(`<nav id="series-nav"><p class="series">${series.parent}</p>`);

    if (series.prev) {
      process.stdout.write(`<p class="series-prev">${series.prev}</p>`);
    }

    if (series.next) {
      process.stdout.write(`<p class="series-next">${series.next}</p>`);
    }

    process.stdout.write('</nav>');
  }

  if (tags) {
    process.stdout.write('<div id="tags-list">');
    tags.forEach(tag => {
      process.stdout.write(`${icon('tag')}&nbsp;<a class="tag" href="/tags/${tag}.html">${tag}</a> `);
    });
    process.stdout.write('</div>');
  }

  process.stdout.write(`<article>${document}</article>`);
})
