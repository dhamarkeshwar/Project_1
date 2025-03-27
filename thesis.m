// Define the function f(t, l) = 3*n^2 + (l - t - 2)*n - t*l
n := 10;  // Set n as a constant
f := func< t, l | 3*n^2 + (l - t - 2)*n - t*l >;

// Define the range for t and l
t_min := 1; t_max := n;
l_min := 1; l_max := n;

// Create the surface plot
P := SurfacePlot(f, t_min, t_max, l_min, l_max);

// Display the plot
P;
