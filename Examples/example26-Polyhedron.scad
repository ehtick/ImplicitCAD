module pyramid(base, height) {
  half = base / 2;

  polyhedron(
    points = [
      [-half, -half, 0],
      [ half, -half, 0],
      [ half,  half, 0],
      [-half,  half, 0],
      [0, 0, height]
    ],
    faces = [
      [0, 1, 2, 3],
      [0, 1, 4],
      [1, 2, 4],
      [2, 3, 4],
      [3, 0, 4]
    ]
  );
}

pyramid_base = 12;
pyramid_height = 14;
pyramid(pyramid_base, pyramid_height);
