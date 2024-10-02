use getargs::Options;
use std::hint::black_box;

fn main() {
    // - long flag with no value
    // - long flag with embedded value
    // - long flag with following value
    // - long flag with optional value (present)
    // - long flag with optional value (not present)
    // - short flag with no value
    // - short flag with embedded value
    // - short flag with following value
    // - short flag with optional value (present)
    // - short flag with optional value (not present)
    // - ridiculously large short flag cluster

    let long_flag_no_value = (0usize..1_000_000).map(|_| "--long-flag-with-no-value");
    let long_flag_embedded_value =
        (0usize..1_000_000).map(|_| "--long-flag-with-embedded-value=value");
    let long_flag_following_value =
        (0usize..1_000_000).flat_map(|_| ["--long-flag-with-following-value", "value"]);
    let long_flag_with_optional_value =
        (0usize..1_000_000).map(|_| "--long-flag-with-optional-value=value");
    let long_flag_without_optional_value =
        (0usize..1_000_000).map(|_| "--long-flag-without-optional-value");
    let short_flag_no_value = (0usize..1_000_000).map(|_| "-s");
    let short_flag_embedded_value = (0usize..1_000_000).map(|_| "-svalue");
    let short_flag_following_value = (0usize..1_000_000).flat_map(|_| ["-s", "value"]);
    let short_flag_with_optional_value = (0usize..1_000_000).map(|_| "-svalue");
    let short_flag_without_optional_value = (0usize..1_000_000).map(|_| "-s");
    let huge_short_flag_cluster =
        (0usize..1_000_000).map(|_| "-pwbc9xba39boz0n02gnz02m9tefgf022bmz987f3nl");

    let mut opts = Options::new(long_flag_no_value);

    while let Some(opt) = opts.next_opt().unwrap() {
        let _ = black_box(opt);
    }

    let mut opts = Options::new(long_flag_embedded_value);

    while let Some(opt) = opts.next_opt().unwrap() {
        let _ = black_box(opt);
        let _ = black_box(opts.value());
    }

    let mut opts = Options::new(long_flag_following_value);

    while let Some(opt) = opts.next_opt().unwrap() {
        let _ = black_box(opt);
        let _ = black_box(opts.value());
    }

    let mut opts = Options::new(long_flag_with_optional_value);

    while let Some(opt) = opts.next_opt().unwrap() {
        let _ = black_box(opt);
        let _ = black_box(opts.value_opt());
    }

    let mut opts = Options::new(long_flag_without_optional_value);

    while let Some(opt) = opts.next_opt().unwrap() {
        let _ = black_box(opt);
        let _ = black_box(opts.value_opt());
    }

    let mut opts = Options::new(short_flag_no_value);

    while let Some(opt) = opts.next_opt().unwrap() {
        let _ = black_box(opt);
    }

    let mut opts = Options::new(short_flag_embedded_value);

    while let Some(opt) = opts.next_opt().unwrap() {
        let _ = black_box(opt);
        let _ = black_box(opts.value());
    }

    let mut opts = Options::new(short_flag_following_value);

    while let Some(opt) = opts.next_opt().unwrap() {
        let _ = black_box(opt);
        let _ = black_box(opts.value());
    }

    let mut opts = Options::new(short_flag_with_optional_value);

    while let Some(opt) = opts.next_opt().unwrap() {
        let _ = black_box(opt);
        let _ = black_box(opts.value_opt());
    }

    let mut opts = Options::new(short_flag_without_optional_value);

    while let Some(opt) = opts.next_opt().unwrap() {
        let _ = black_box(opt);
        let _ = black_box(opts.value_opt());
    }

    let mut opts = Options::new(huge_short_flag_cluster);

    while let Some(opt) = opts.next_opt().unwrap() {
        let _ = black_box(opt);
    }
}
