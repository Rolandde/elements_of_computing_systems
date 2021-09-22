extern crate minifb;

use minifb::{Key, Window, WindowOptions};

const WIDTH: usize = 512;
const HEIGHT: usize = 256;

fn main() {
    let mut args =  std::env::args();
    args.next(); // Program name
    let file = args.next().expect("No file specified");
    let rom = hack_tools::hack_io::write_rom_from_file(file);
    let mut comp = hack_kernel::Computer::new(rom);
    let mut debug = hack_tools::Debugger::new(&mut comp);
    debug.write_memory(0.into(), 10.into());

    let mut buffer: Vec<u32> = vec![0; WIDTH * HEIGHT];

    let mut window = Window::new(
        "Test - ESC to exit",
        WIDTH,
        HEIGHT,
        WindowOptions::default(),
    )
    .unwrap_or_else(|e| {
        panic!("{}", e);
    });

    // Limit to max ~60 fps update rate
    window.limit_update_rate(Some(std::time::Duration::from_micros(16600)));

    while window.is_open() && !window.is_key_down(Key::Escape) {
        debug.computer().cycle(false);

        for (pos, pixel) in hack_tools::Scan::new(&debug.computer()).enumerate() {
            if pixel {
                buffer[pos] = 0
            } else {
                buffer[pos] = 4294967295; // write something more funny here!
            }
        }

        // We unwrap here as we want this code to exit if it fails. Real applications may want to handle this in a different way
        window
            .update_with_buffer(&buffer, WIDTH, HEIGHT)
            .unwrap();
    }
}