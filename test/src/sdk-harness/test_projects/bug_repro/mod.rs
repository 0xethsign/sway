use test_helpers::script_runner;

#[tokio::test]
async fn contract_id_eq_implementation() {
    let path_to_bin = "test_projects/bug_repro/out/debug/bug_repro.bin";
    let return_val = script_runner(path_to_bin).await;
    assert_eq!(1, return_val);
}