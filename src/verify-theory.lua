local theory = {
	assertion_t = "Assertion",
	satisfaction_t = "any",
}

function theory:satisfactions(assignment, truth)
	assertis(assignment, mapType("Assertion", "boolean"))

	-- TODO

	return {assignment}
end

function theory:breakup(assertion, target)
	assertis(assertion, "Assertion")

	if assertion.tag == "method" then
		if assertion.methodName == "and" then
			if target == true then
				local truths = {{true, true}}
				return {assertion.base, assertion.arguments[1]}, truths
			else
				local truths = {{false, false}, {false, true}, {true, false}}
				return {assertion.base, assertion.arguments[1]}, truths
			end
		elseif assertion.methodName == "not" then
			if target == true then
				local truths = {{false}}
				return {assertion.base}, truths
			else
				local truths = {{true}}
				return {assertion.base}, truths
			end
		end
	end

	return false
end

return theory
