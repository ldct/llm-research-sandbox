export type FrameworkId =
  | 'flexbox'
  | 'grid'
  | 'swiftui'
  | 'compose'
  | 'flutter';

export type Framework = {
  id: FrameworkId;
  label: string;
  lang: string;
  live: boolean;
};

export const frameworks: Framework[] = [
  { id: 'flexbox', label: 'CSS Flexbox', lang: 'css', live: true },
  { id: 'grid', label: 'CSS Grid', lang: 'css', live: true },
  { id: 'swiftui', label: 'SwiftUI', lang: 'swift', live: false },
  { id: 'compose', label: 'Jetpack Compose', lang: 'kotlin', live: false },
  { id: 'flutter', label: 'Flutter', lang: 'dart', live: false },
];

export type Difficulty = 'trivial' | 'easy' | 'medium' | 'gotcha';

export type Implementation = {
  code: string;
  difficulty: Difficulty;
  notes?: string;
};

export type Layout = {
  slug: string;
  title: string;
  tier: number;
  tagline: string;
  description: string;
  invariants: string[];
  implementations: Record<FrameworkId, Implementation>;
};

export const layouts: Layout[] = [
  {
    slug: 'centered',
    title: 'Centered',
    tier: 1,
    tagline: 'A single child, horizontally and vertically centered in its container.',
    description:
      'The classic "center a div" problem. One child sits at the geometric center of a fixed-size container.',
    invariants: [
      'Child is centered on both axes regardless of its intrinsic size.',
      'Changing the container size keeps the child centered.',
      'Changing the child size keeps the child centered.',
    ],
    implementations: {
      flexbox: {
        difficulty: 'trivial',
        code: `.container {
  display: flex;
  justify-content: center;   /* horizontal */
  align-items: center;       /* vertical */
  height: 240px;
}`,
      },
      grid: {
        difficulty: 'trivial',
        code: `.container {
  display: grid;
  place-items: center;       /* both axes at once */
  height: 240px;
}`,
        notes: 'place-items is a shorthand for align-items + justify-items.',
      },
      swiftui: {
        difficulty: 'trivial',
        code: `ZStack {
    Text("Hi")
}
.frame(maxWidth: .infinity, maxHeight: .infinity)`,
        notes:
          'ZStack centers by default. The outer .frame expands the ZStack to fill available space.',
      },
      compose: {
        difficulty: 'trivial',
        code: `Box(
    modifier = Modifier.fillMaxSize(),
    contentAlignment = Alignment.Center,
) {
    Text("Hi")
}`,
      },
      flutter: {
        difficulty: 'trivial',
        code: `Center(
  child: Text('Hi'),
)`,
        notes: 'Center is just syntactic sugar for Align(alignment: Alignment.center).',
      },
    },
  },
  {
    slug: 'equal-horizontal',
    title: 'Equal Horizontal Distribution',
    tier: 1,
    tagline: 'Fixed height; children fill the row with equal widths, no spacing.',
    description:
      'Children are arranged in a row, each taking an equal share of the available width, with no gap between them. Common for segmented controls, full-width button bars.',
    invariants: [
      'All children have the same width.',
      'Children together fill 100% of the container width.',
      'No space between children.',
      'Adding a child reduces each existing child\'s width proportionally.',
    ],
    implementations: {
      flexbox: {
        difficulty: 'trivial',
        code: `.container {
  display: flex;
  height: 80px;
}
.container > * {
  flex: 1;                   /* grow equally from 0 basis */
}`,
      },
      grid: {
        difficulty: 'trivial',
        code: `.container {
  display: grid;
  grid-auto-flow: column;
  grid-auto-columns: 1fr;    /* each implicit column gets 1 fraction */
  height: 80px;
}`,
      },
      swiftui: {
        difficulty: 'easy',
        code: `HStack(spacing: 0) {
    ForEach(items) { item in
        ItemView(item)
            .frame(maxWidth: .infinity)
    }
}
.frame(height: 80)`,
        notes:
          'Each child needs .frame(maxWidth: .infinity) to claim equal share — without it, HStack sizes children to their intrinsic width.',
      },
      compose: {
        difficulty: 'easy',
        code: `Row(
    modifier = Modifier.fillMaxWidth().height(80.dp),
) {
    items.forEach { item ->
        ItemView(
            item,
            modifier = Modifier.weight(1f).fillMaxHeight(),
        )
    }
}`,
        notes: 'weight(1f) on each child is the Compose equivalent of flex: 1.',
      },
      flutter: {
        difficulty: 'easy',
        code: `Row(
  children: items
      .map((i) => Expanded(child: ItemView(i)))
      .toList(),
)`,
        notes: 'Expanded is shorthand for Flexible(fit: FlexFit.tight, flex: 1).',
      },
    },
  },
  {
    slug: 'equal-horizontal-gap',
    title: 'Equal Horizontal + Gap',
    tier: 1,
    tagline: 'Same as equal horizontal, but with a fixed gap between children.',
    description:
      'Children take equal width and are separated by a uniform gap. The gap eats into the available space; each child is (containerWidth − totalGap) / n.',
    invariants: [
      'Uniform gap between every adjacent pair of children.',
      'No leading or trailing gap.',
      'All children remain equal width as the container resizes.',
    ],
    implementations: {
      flexbox: {
        difficulty: 'trivial',
        code: `.container {
  display: flex;
  gap: 12px;                 /* modern flexbox gap */
  height: 80px;
}
.container > * {
  flex: 1;
}`,
      },
      grid: {
        difficulty: 'trivial',
        code: `.container {
  display: grid;
  grid-auto-flow: column;
  grid-auto-columns: 1fr;
  gap: 12px;
  height: 80px;
}`,
      },
      swiftui: {
        difficulty: 'trivial',
        code: `HStack(spacing: 12) {
    ForEach(items) { item in
        ItemView(item)
            .frame(maxWidth: .infinity)
    }
}
.frame(height: 80)`,
        notes: 'HStack spacing handles the gap natively.',
      },
      compose: {
        difficulty: 'trivial',
        code: `Row(
    modifier = Modifier.fillMaxWidth().height(80.dp),
    horizontalArrangement = Arrangement.spacedBy(12.dp),
) {
    items.forEach { item ->
        ItemView(item, modifier = Modifier.weight(1f))
    }
}`,
      },
      flutter: {
        difficulty: 'gotcha',
        code: `// Flutter's Row has no built-in gap. Options:

// 1. Interleave SizedBox manually:
Row(
  children: [
    for (var i = 0; i < items.length; i++) ...[
      if (i > 0) const SizedBox(width: 12),
      Expanded(child: ItemView(items[i])),
    ],
  ],
)

// 2. Or pad each child and compensate on the container:
Padding(
  padding: const EdgeInsets.symmetric(horizontal: -6),
  child: Row(
    children: items
        .map((i) => Expanded(
              child: Padding(
                padding: const EdgeInsets.symmetric(horizontal: 6),
                child: ItemView(i),
              ),
            ))
        .toList(),
  ),
)`,
        notes:
          'This is a genuine rough edge. CSS/SwiftUI/Compose all have first-class gap/spacing; Flutter expects you to interleave spacer widgets. The first approach is more idiomatic.',
      },
    },
  },
  {
    slug: 'vertical-stack',
    title: 'Vertical Stack',
    tier: 1,
    tagline: 'Children stacked vertically with a uniform gap.',
    description:
      'The vertical twin of a row: each child sits below the previous one, separated by a fixed gap. Intrinsic heights preserved.',
    invariants: [
      'Each child sits directly below the previous one.',
      'Uniform gap between siblings.',
      'Children keep their intrinsic height.',
    ],
    implementations: {
      flexbox: {
        difficulty: 'trivial',
        code: `.container {
  display: flex;
  flex-direction: column;
  gap: 12px;
}`,
      },
      grid: {
        difficulty: 'trivial',
        code: `.container {
  display: grid;
  gap: 12px;                 /* single column by default */
}`,
      },
      swiftui: {
        difficulty: 'trivial',
        code: `VStack(spacing: 12) {
    ForEach(items) { item in
        ItemView(item)
    }
}`,
      },
      compose: {
        difficulty: 'trivial',
        code: `Column(
    verticalArrangement = Arrangement.spacedBy(12.dp),
) {
    items.forEach { item ->
        ItemView(item)
    }
}`,
      },
      flutter: {
        difficulty: 'gotcha',
        code: `// Same gap-gotcha as Row. Idiomatic:
Column(
  children: [
    for (var i = 0; i < items.length; i++) ...[
      if (i > 0) const SizedBox(height: 12),
      ItemView(items[i]),
    ],
  ],
)`,
        notes: 'Flutter 3.27+ added a gap parameter to Flex, but older code still uses SizedBox spacers.',
      },
    },
  },
  {
    slug: 'sidebar',
    title: 'Sidebar + Content',
    tier: 2,
    tagline: 'Fixed-width sidebar on the left; content fills the remaining space.',
    description:
      'A two-column layout where the first column has a fixed width and the second column absorbs all remaining horizontal space.',
    invariants: [
      'Sidebar stays at its fixed width regardless of container size.',
      'Content column grows to fill the remainder.',
      'Both columns share the same height.',
    ],
    implementations: {
      flexbox: {
        difficulty: 'trivial',
        code: `.container {
  display: flex;
  height: 240px;
}
.sidebar {
  flex: 0 0 200px;           /* no grow, no shrink, 200px basis */
}
.content {
  flex: 1;
}`,
      },
      grid: {
        difficulty: 'trivial',
        code: `.container {
  display: grid;
  grid-template-columns: 200px 1fr;
  height: 240px;
}`,
        notes: 'Reads almost like the visual intent: "fixed, then flex".',
      },
      swiftui: {
        difficulty: 'easy',
        code: `HStack(spacing: 0) {
    Sidebar()
        .frame(width: 200)
    Content()
        .frame(maxWidth: .infinity)
}`,
      },
      compose: {
        difficulty: 'easy',
        code: `Row(modifier = Modifier.fillMaxSize()) {
    Sidebar(modifier = Modifier.width(200.dp))
    Content(modifier = Modifier.weight(1f))
}`,
      },
      flutter: {
        difficulty: 'easy',
        code: `Row(
  children: [
    SizedBox(width: 200, child: Sidebar()),
    Expanded(child: Content()),
  ],
)`,
      },
    },
  },
  {
    slug: 'sticky-footer',
    title: 'Sticky Footer',
    tier: 2,
    tagline: 'Header, content, footer — footer hugs the bottom even when content is short.',
    description:
      'When content is short, the footer sits at the bottom of the viewport. When content is long, the footer is pushed down and scrolls into view naturally.',
    invariants: [
      'Footer is always below content.',
      'When content height < viewport, footer still sits at the bottom.',
      'When content height > viewport, content scrolls; footer follows.',
    ],
    implementations: {
      flexbox: {
        difficulty: 'easy',
        code: `body {
  min-height: 100vh;
  display: flex;
  flex-direction: column;
}
main {
  flex: 1;                   /* absorb extra vertical space */
}`,
      },
      grid: {
        difficulty: 'easy',
        code: `body {
  min-height: 100vh;
  display: grid;
  grid-template-rows: auto 1fr auto;
}`,
        notes: 'Arguably the clearest expression: "header auto, content 1fr, footer auto".',
      },
      swiftui: {
        difficulty: 'easy',
        code: `VStack(spacing: 0) {
    Header()
    Content()
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    Footer()
}`,
      },
      compose: {
        difficulty: 'easy',
        code: `Column(modifier = Modifier.fillMaxSize()) {
    Header()
    Content(modifier = Modifier.weight(1f))
    Footer()
}`,
      },
      flutter: {
        difficulty: 'easy',
        code: `Column(
  children: [
    Header(),
    Expanded(child: Content()),
    Footer(),
  ],
)`,
      },
    },
  },
  {
    slug: 'centered-column',
    title: 'Centered Reading Column',
    tier: 2,
    tagline: 'A column centered on the page, capped at a maximum width.',
    description:
      'Content is horizontally centered with a maximum width. When the viewport is narrower than the max, content fills the viewport. When wider, content stays at max-width with equal margins on both sides.',
    invariants: [
      'Content never exceeds max-width.',
      'When viewport < max-width, content fills viewport.',
      'When viewport ≥ max-width, content is horizontally centered.',
    ],
    implementations: {
      flexbox: {
        difficulty: 'trivial',
        code: `.column {
  max-width: 680px;
  margin-inline: auto;       /* classic centering */
}`,
        notes:
          'Flexbox is overkill here — plain margin auto is the idiomatic CSS solution.',
      },
      grid: {
        difficulty: 'easy',
        code: `.page {
  display: grid;
  grid-template-columns:
    1fr min(680px, 100%) 1fr;
}
.column {
  grid-column: 2;
}`,
        notes:
          'The "1fr min(680px, 100%) 1fr" pattern scales content and centers without hard-coding the max-width twice.',
      },
      swiftui: {
        difficulty: 'easy',
        code: `VStack {
    Text("Lorem ipsum...")
}
.frame(maxWidth: 680)
.frame(maxWidth: .infinity, alignment: .center)`,
        notes:
          'Two .frame modifiers: inner caps the width, outer pushes the capped frame into a full-width container so it centers.',
      },
      compose: {
        difficulty: 'easy',
        code: `Box(
    modifier = Modifier.fillMaxWidth(),
    contentAlignment = Alignment.TopCenter,
) {
    Column(modifier = Modifier.widthIn(max = 680.dp)) {
        Text("Lorem ipsum...")
    }
}`,
      },
      flutter: {
        difficulty: 'easy',
        code: `Center(
  child: ConstrainedBox(
    constraints: const BoxConstraints(maxWidth: 680),
    child: Column(children: [Text('Lorem ipsum...')]),
  ),
)`,
      },
    },
  },
  {
    slug: 'card-grid',
    title: 'Wrapping Card Grid',
    tier: 2,
    tagline: 'Cards of equal width that wrap to new rows as the container shrinks.',
    description:
      'Cards have a minimum comfortable width. As many cards as fit per row do; the rest wrap. Every card in a row has equal width.',
    invariants: [
      'Every card has a minimum width (cards never become unreadably narrow).',
      'Cards in the same row have equal widths.',
      'When space is tight, cards wrap to a new row.',
      'Uniform gap between cards both horizontally and vertically.',
    ],
    implementations: {
      flexbox: {
        difficulty: 'medium',
        code: `.grid {
  display: flex;
  flex-wrap: wrap;
  gap: 16px;
}
.card {
  flex: 1 1 220px;           /* grow + shrink, min basis 220px */
}`,
        notes:
          'Subtle gotcha: the last row\'s cards stretch to fill the row. Usually fine; for a "ragged last row", use grid instead.',
      },
      grid: {
        difficulty: 'easy',
        code: `.grid {
  display: grid;
  grid-template-columns:
    repeat(auto-fill, minmax(220px, 1fr));
  gap: 16px;
}`,
        notes:
          'auto-fit vs auto-fill matters: auto-fill keeps empty tracks; auto-fit collapses them so surviving cards stretch.',
      },
      swiftui: {
        difficulty: 'easy',
        code: `LazyVGrid(
    columns: [GridItem(.adaptive(minimum: 220), spacing: 16)],
    spacing: 16,
) {
    ForEach(items) { item in
        CardView(item)
    }
}`,
        notes: '.adaptive(minimum:) is the direct analog of CSS minmax(220px, 1fr).',
      },
      compose: {
        difficulty: 'easy',
        code: `LazyVerticalGrid(
    columns = GridCells.Adaptive(minSize = 220.dp),
    verticalArrangement = Arrangement.spacedBy(16.dp),
    horizontalArrangement = Arrangement.spacedBy(16.dp),
) {
    items(cards) { card ->
        CardView(card)
    }
}`,
      },
      flutter: {
        difficulty: 'easy',
        code: `GridView.extent(
  maxCrossAxisExtent: 260,
  mainAxisSpacing: 16,
  crossAxisSpacing: 16,
  childAspectRatio: 1.6,
  children: cards.map((c) => CardView(c)).toList(),
)`,
        notes:
          'Flutter pins aspect ratio per cell (childAspectRatio) rather than letting content decide height. Different mental model from CSS Grid.',
      },
    },
  },
];

export const layoutBySlug = (slug: string) =>
  layouts.find((l) => l.slug === slug);
